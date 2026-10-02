//! A bounded overapproximation of the Boolean structure above expensive predicates.
//!
//! An unavailable word makes its enclosing predicate an independent Boolean input. Small masks
//! and single-bit extracts can instead project only the requested bits. Repeated predicates
//! and bit projections share inputs. A constant true output therefore holds for every assignment
//! of the original predicates too. The validity shortcut uses only that result; other results
//! fall back to the full circuit for real symbol assignments and SAT search. The joint-domain
//! service separately enumerates small cuts to recover conservative output tuple sets.

use super::{
    Blaster,
    aig::{Aig, FALSE, L, TRUE},
    blast::Bits,
};
use crate::{Context, expr::OpCode, hash::IdMap};

const VISITS: usize = 256;
const GATES: usize = 4096;
const WORK: usize = 16_384;

pub(super) fn constant_true(cx: &mut Context, root: u32) -> bool {
    // Atomic questions and small expressions rarely have a useful Boolean cut.
    if cx.height(cx.handle(root)).unwrap_or(0) < 4 {
        return false;
    }
    let mut probe = Probe::new(cx, VISITS, GATES, WORK);
    let Some(bits) = probe.word(root) else {
        return false;
    };
    let graph = &probe.blaster.g;
    if graph.len() > GATES || bits.len() != 1 || bits[0] == FALSE {
        return false;
    }
    if bits[0] == TRUE {
        return true;
    }
    // Structural hashing need not collapse every small Boolean tautology. Check the
    // entire cut, never a sample of original symbols, under a separate fixed allowance.
    let (support, inputs) = graph.input_support(&bits);
    if inputs > 8 {
        return false;
    }
    let assignments = 1usize << inputs;
    if assignments.div_ceil(64) * graph.len() > WORK {
        return false;
    }
    for base in (0..assignments).step_by(64) {
        let lanes = (assignments - base).min(64);
        let mask = if lanes == 64 {
            u64::MAX
        } else {
            (1u64 << lanes) - 1
        };
        let values = graph.eval_assignment_batch(&support, base);
        if Aig::word(&values, bits[0]) & mask != mask {
            return false;
        }
    }
    true
}

pub(super) struct Probe<'a> {
    pub(super) blaster: Blaster<'a>,
    unavailable: IdMap<u32, ()>,
    projected: IdMap<(u32, usize), L>,
    visits: usize,
    work: usize,
    gates: usize,
}

impl<'a> Probe<'a> {
    pub(super) fn new(cx: &'a mut Context, visits: usize, gates: usize, work: usize) -> Self {
        Self {
            blaster: Blaster::new(cx, gates),
            unavailable: IdMap::default(),
            projected: IdMap::default(),
            // This also bounds recursive stack depth, even for a very deep input DAG.
            visits: visits.min(VISITS),
            work,
            gates,
        }
    }

    fn opaque(&mut self, id: u32) -> Option<Bits> {
        if self.blaster.cx.wid(id) == 1 {
            let bits = vec![self.blaster.g.input()];
            self.blaster.bits.insert(id, bits.clone());
            Some(bits)
        } else {
            self.unavailable.insert(id, ());
            None
        }
    }

    // A projected bit is an overapproximation, never an original-symbol assignment.
    // Following pure wiring preserves overlap and complements without expanding a wide
    // source. Other operations receive shared opaque bit inputs. Every original valuation
    // extends to a valuation of these inputs, so a universally true cut remains sound.
    fn project_bit(&mut self, id: u32, bit: usize) -> L {
        if let Some(bits) = self.blaster.bits.get(&id) {
            return bits[bit];
        }
        if let Some(&value) = self.projected.get(&(id, bit)) {
            return value;
        }
        let node = self.blaster.cx.node(id);
        let value = if self.visits == 0 {
            self.blaster.g.input()
        } else {
            self.visits -= 1;
            match node.op {
                OpCode::Const => {
                    if self.blaster.cx.const_val(id).unwrap().bit(bit as u16) == Some(true) {
                        TRUE
                    } else {
                        FALSE
                    }
                }
                OpCode::Sym => match self.blaster.cx.declared_at(id) {
                    Some(k) if k.known_one().bit(bit as u16) == Some(true) => TRUE,
                    Some(k) if k.known_zero().bit(bit as u16) == Some(true) => FALSE,
                    _ => self.blaster.g.input(),
                },
                OpCode::Not => self.project_bit(node.a, bit) ^ 1,
                OpCode::Extract => self.project_bit(node.a, bit + node.b as usize),
                OpCode::Zext => {
                    if bit < usize::from(self.blaster.cx.wid(node.a)) {
                        self.project_bit(node.a, bit)
                    } else {
                        FALSE
                    }
                }
                OpCode::Sext => self.project_bit(
                    node.a,
                    bit.min(usize::from(self.blaster.cx.wid(node.a)) - 1),
                ),
                OpCode::Concat => {
                    let low = usize::from(self.blaster.cx.wid(node.b));
                    if bit < low {
                        self.project_bit(node.b, bit)
                    } else {
                        self.project_bit(node.a, bit - low)
                    }
                }
                _ => self.blaster.g.input(),
            }
        };
        self.projected.insert((id, bit), value);
        value
    }

    // Recursion is bounded by VISITS, independently of the original DAG's depth. A failed
    // wide child stops descent immediately; there is no traversal of its remaining siblings.
    pub(super) fn word(&mut self, id: u32) -> Option<Bits> {
        if let Some(bits) = self.blaster.bits.get(&id) {
            return Some(bits.clone());
        }
        if self.unavailable.contains_key(&id) {
            return None;
        }
        if self.visits == 0 || self.blaster.g.len() > self.gates {
            return self.opaque(id);
        }
        self.visits -= 1;
        let node = self.blaster.cx.node(id);
        let width = usize::from(node.width);
        let supported = match node.op {
            OpCode::Const => true,
            OpCode::Sym => {
                width == 1
                    || self
                        .blaster
                        .cx
                        .declared_at(id)
                        .is_some_and(|k| k.as_constant().is_some())
            }
            OpCode::Not
            | OpCode::Neg
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract
            | OpCode::Concat
            | OpCode::Select
            | OpCode::Eq
            | OpCode::Ne
            | OpCode::Ult
            | OpCode::Ule
            | OpCode::Slt
            | OpCode::Sle
            | OpCode::Add
            | OpCode::Sub
            | OpCode::Mul
            | OpCode::And
            | OpCode::Or
            | OpCode::Xor
            | OpCode::Shl
            | OpCode::LShr
            | OpCode::AShr => true,
            _ => false,
        };
        if !supported {
            return self.opaque(id);
        }
        if node.op == OpCode::Extract && width == 1 && self.work != 0 {
            self.work -= 1;
            let bits = vec![self.project_bit(node.a, node.b as usize)];
            self.blaster.bits.insert(id, bits.clone());
            return Some(bits);
        }
        if node.op == OpCode::And {
            // A narrow mask needs only the source bits it keeps. Expanding the source
            // word would either fail outright or retain hundreds of irrelevant inputs.
            let left = self.word(node.a);
            let right = self.word(node.b);
            let masked = match (left, right) {
                (Some(bits), None) => Some((bits, node.b)),
                (None, Some(bits)) => Some((bits, node.a)),
                _ => None,
            };
            if let Some((bits, other)) = masked {
                let live = bits.iter().filter(|&&bit| bit != FALSE).count();
                let cost = width.saturating_mul(8);
                if live > 8 || cost > self.work {
                    return self.opaque(id);
                }
                self.work -= cost;
                let mut out = Vec::with_capacity(width);
                for (i, bit) in bits.into_iter().enumerate() {
                    out.push(if bit == FALSE {
                        FALSE
                    } else {
                        let input = self.project_bit(other, i);
                        self.blaster.g.and(bit, input)
                    });
                }
                self.blaster.bits.insert(id, out.clone());
                return Some(out);
            }
        }
        for child in node.children() {
            if self.word(child).is_none() {
                return self.opaque(id);
            }
        }
        let cost = match node.op {
            OpCode::Const
            | OpCode::Sym
            | OpCode::Not
            | OpCode::Zext
            | OpCode::Sext
            | OpCode::Extract
            | OpCode::Concat => width,
            OpCode::Mul
                if super::blast::binary_factor(
                    &self.blaster.bits[&node.a],
                    &self.blaster.bits[&node.b],
                )
                .is_some() =>
            {
                width
            }
            OpCode::Mul => width.saturating_mul(width),
            _ => width.saturating_mul(8),
        };
        if cost > self.work {
            return self.opaque(id);
        }
        self.work -= cost;
        match self.blaster.node(id) {
            Ok(bits) => {
                self.blaster.bits.insert(id, bits.clone());
                Some(bits)
            }
            Err(_) => self.opaque(id),
        }
    }
}
