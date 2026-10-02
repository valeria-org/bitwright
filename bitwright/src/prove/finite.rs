//! Optional, exhaustively checked finite-domain facts for keyed integer pairs.
//!
//! Verification is separate from query work and may be expensive. No fact is accepted from
//! an unchecked candidate list, and no fact narrows an unrestricted source implicitly.
//!
//! ```
//! use bitwright::prove::finite::{CheckedPair, VerifyLimits};
//! let checked = CheckedPair::verify([3, 5], 0, u64::MAX, 8, VerifyLimits::default())?;
//! assert!(checked.candidates().is_empty());
//! // Pass the prepared value explicitly to Question::valid_with_pairs.
//! # Ok::<(), Box<dyn std::error::Error>>(())
//! ```

use crate::{BitVec, Context, Error, Expr, Width, expr::OpCode, hash::IdMap};

/// Limits for producing a complete finite-domain fact.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct VerifyLimits {
    /// Largest complete domain to enumerate. Insufficient allowance fails before enumeration.
    pub inputs: u64,
    /// Maximum number of satisfying inputs retained. Exceeding it produces no fact.
    pub candidates: usize,
}

impl Default for VerifyLimits {
    fn default() -> Self {
        Self {
            inputs: 65_536,
            candidates: 256,
        }
    }
}

/// A finite fact was not completely checked.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum VerifyError {
    /// Exhaustive domains beyond 32 bits are not supported.
    DomainTooWide(u8),
    /// The complete domain exceeds the requested allowance.
    Budget { required: u64, allowed: u64 },
    /// Too many satisfying inputs were found; the incomplete result is discarded.
    TooManyCandidates(usize),
}

impl core::fmt::Display for VerifyError {
    fn fmt(&self, f: &mut core::fmt::Formatter<'_>) -> core::fmt::Result {
        write!(f, "finite-domain verification incomplete: {self:?}")
    }
}
impl std::error::Error for VerifyError {}

/// Complete preimages of a masked pair on `0 <= x < 2^domain_bits`.
///
/// The 64-bit wrapping mixer is `k * (h XOR ((h >> 32) >> (h >> 60)))`, where
/// `h = k * (x XOR k)`. Both shifts are logical. Fields are private: creation requires
/// complete scalar enumeration through [`verify`](Self::verify).
#[derive(Clone, Debug)]
pub struct CheckedPair {
    keys: [u64; 2],
    salt: u64,
    mask: u64,
    domain_bits: u8,
    candidates: Vec<u64>,
}

#[inline(always)]
fn mixer(key: u64, x: u64) -> u64 {
    let h = key.wrapping_mul(x ^ key);
    key.wrapping_mul(h ^ ((h >> 32) >> (h >> 60)))
}

impl CheckedPair {
    /// Check every input in the stated domain, retaining exactly those with
    /// `(F_a(x) XOR F_b(x) XOR salt) AND mask == 0`.
    ///
    /// This is intended for explicit preparation. A 32-bit domain requires 2^32 evaluations;
    /// its cold verification cost is not part of a subsequent query's SAT statistics.
    pub fn verify(
        keys: [u64; 2],
        salt: u64,
        mask: u64,
        domain_bits: u8,
        limits: VerifyLimits,
    ) -> Result<Self, VerifyError> {
        if domain_bits > 32 {
            return Err(VerifyError::DomainTooWide(domain_bits));
        }
        let required = 1u64 << domain_bits;
        if required > limits.inputs {
            return Err(VerifyError::Budget {
                required,
                allowed: limits.inputs,
            });
        }
        let mut candidates = Vec::new();
        for x in 0..required {
            if (mixer(keys[0], x) ^ mixer(keys[1], x) ^ salt) & mask == 0 {
                if candidates.len() == limits.candidates {
                    return Err(VerifyError::TooManyCandidates(limits.candidates));
                }
                candidates.push(x);
            }
        }
        Ok(Self {
            keys,
            salt,
            mask,
            domain_bits,
            candidates,
        })
    }

    /// Every satisfying input in the fully verified domain, in numeric order.
    pub fn candidates(&self) -> &[u64] {
        &self.candidates
    }

    /// Apply this fact to a bounded integer DAG, returning an equivalent predicate.
    ///
    /// Matching requires exact mixer semantics, a shared source, and a syntactically or
    /// declaratively established source bound. The original predicate is checked again at
    /// every candidate. Other symbols remain in guarded residual predicates. Unsupported
    /// patterns or exhausted rewrite work leave the predicate unchanged.
    pub fn simplify(&self, cx: &mut Context, predicate: Expr) -> Result<Expr, Error> {
        let root = cx.id(predicate)?;
        let remaining = std::cell::Cell::new(4096usize);
        let truncated = std::cell::Cell::new(false);
        let order = cx.post_order_ids_pruned(&[root], |_| {
            if remaining.get() == 0 {
                truncated.set(true);
                true
            } else {
                remaining.set(remaining.get() - 1);
                false
            }
        });
        if truncated.get() {
            return Ok(predicate);
        }
        let mut rewritten = IdMap::default();
        let mut work = 16_384usize;
        for id in order {
            let node = cx.node(id);
            let mut kids = [node.a, node.b, node.c];
            let mut changed = false;
            for (slot, child) in node.children().enumerate() {
                kids[slot] = rewritten[&child];
                changed |= kids[slot] != child;
            }
            let current = if changed { cx.rebuild(id, kids)? } else { id };
            let next = self
                .reduce_comparison(cx, current, &mut work)?
                .unwrap_or(current);
            let next = fold_boolean_complements(cx, next)?;
            rewritten.insert(id, next);
        }
        Ok(cx.handle(rewritten[&root]))
    }

    fn reduce_comparison(
        &self,
        cx: &mut Context,
        id: u32,
        work: &mut usize,
    ) -> Result<Option<u32>, Error> {
        let node = cx.node(id);
        if !matches!(node.op, OpCode::Eq | OpCode::Ne) {
            return Ok(None);
        }
        let Some((subject, target)) = constant_side(cx, node.a, node.b) else {
            return Ok(None);
        };
        if cx.wid(subject) != 64 {
            return Ok(None);
        }
        let disjunction = cx.node(subject).op == OpCode::Or;
        let mut leaves = vec![subject];
        let mut source = None;
        while let Some(leaf) = leaves.pop() {
            if *work == 0 {
                return Ok(None);
            }
            *work -= 1;
            let n = cx.node(leaf);
            if n.op == OpCode::Or {
                leaves.extend([n.a, n.b]);
                continue;
            }
            // In an OR equality every leaf must be zero at every zero target bit.
            let (term, observed) = if n.op == OpCode::And {
                constant_side(cx, n.a, n.b).unwrap_or((leaf, u64::MAX))
            } else {
                (leaf, u64::MAX)
            };
            let required = if disjunction {
                observed & !target
            } else {
                observed
            };
            if required & self.mask != self.mask {
                continue;
            }
            if let Some((src, salt)) = self.match_pair(cx, term, work)
                && (salt ^ if disjunction { 0 } else { target } ^ self.salt) & self.mask == 0
                && bounded(cx, src, self.domain_bits, &mut 64)
            {
                source = Some(src);
                break;
            }
        }
        let Some(source) = source else {
            return Ok(None);
        };
        // Equality is possible only at a checked candidate. Substitute just that source;
        // dependencies outside it remain inside each guarded original residual.
        let target_node = cx.mk_const(&BitVec::from_u64(Width::W64, target).unwrap())?;
        let equality = cx.c_cmp(crate::CmpOp::Eq, subject, target_node)?;
        let mut result = cx.mk_const(&BitVec::zero(Width::W1))?;
        for &candidate in &self.candidates {
            if *work < 4096 {
                return Ok(None);
            }
            *work -= 4096;
            let value = cx.constant_u64(Width::W64, candidate)?;
            let mut substitution = crate::Substitution::new();
            substitution.replace(cx, cx.handle(source), value)?;
            let Some(replaced) =
                cx.substitute_bounded(&[cx.handle(equality)], &mut substitution, 4096)?
            else {
                return Ok(None);
            };
            let residual = cx.id(replaced[0])?;
            let guard = source_equals(cx, source, candidate)?;
            let alternative = cx.c_bin(crate::BinOp::And, guard, residual)?;
            result = cx.c_bin(crate::BinOp::Or, result, alternative)?;
        }
        if node.op == OpCode::Ne {
            result = cx.c_un(crate::UnOp::Not, result)?;
        }
        Ok(Some(result))
    }

    fn match_pair(&self, cx: &Context, id: u32, work: &mut usize) -> Option<(u32, u64)> {
        let mut stack = vec![id];
        let mut salt = 0;
        let mut terms = Vec::new();
        while let Some(id) = stack.pop() {
            if *work == 0 {
                return None;
            }
            *work -= 1;
            if let Some(value) = constant(cx, id) {
                salt ^= value;
                continue;
            }
            let node = cx.node(id);
            if node.op == OpCode::Xor {
                stack.extend([node.a, node.b]);
            } else {
                terms.push(id);
                if terms.len() > 2 {
                    return None;
                }
            }
        }
        if terms.len() != 2 {
            return None;
        }
        let (ka, a) = match_mixer(cx, terms[0])?;
        let (kb, b) = match_mixer(cx, terms[1])?;
        if a != b
            || !((ka == self.keys[0] && kb == self.keys[1])
                || (ka == self.keys[1] && kb == self.keys[0]))
        {
            return None;
        }
        Some((a, salt))
    }
}

fn constant(cx: &Context, id: u32) -> Option<u64> {
    (cx.wid(id) == 64)
        .then(|| cx.const_val(id)?.to_u64())
        .flatten()
}
fn constant_side(cx: &Context, a: u32, b: u32) -> Option<(u32, u64)> {
    constant(cx, a)
        .map(|k| (b, k))
        .or_else(|| constant(cx, b).map(|k| (a, k)))
}
fn count_of(cx: &Context, mut id: u32, h: u32) -> bool {
    let node = cx.node(id);
    if node.op == OpCode::And {
        let Some((value, 63)) = constant_side(cx, node.a, node.b) else {
            return false;
        };
        id = value;
    }
    let node = cx.node(id);
    node.op == OpCode::LShr && node.a == h && constant(cx, node.b) == Some(60)
}
fn match_mixer(cx: &Context, id: u32) -> Option<(u64, u32)> {
    let outer = cx.node(id);
    if outer.op != OpCode::Mul || outer.width != 64 {
        return None;
    }
    let (scrambled, key) = constant_side(cx, outer.a, outer.b)?;
    let xor = cx.node(scrambled);
    if xor.op != OpCode::Xor {
        return None;
    }
    for (h, shifted) in [(xor.a, xor.b), (xor.b, xor.a)] {
        let shift = cx.node(shifted);
        if shift.op != OpCode::LShr {
            continue;
        }
        let nested = cx.node(shift.a);
        let good =
            if nested.op == OpCode::LShr && nested.a == h && constant(cx, nested.b) == Some(32) {
                count_of(cx, shift.b, h)
            } else if shift.a == h && cx.node(shift.b).op == OpCode::Add {
                let add = cx.node(shift.b);
                constant_side(cx, add.a, add.b)
                    .is_some_and(|(count, offset)| offset == 32 && count_of(cx, count, h))
            } else {
                false
            };
        if !good {
            continue;
        }
        let inner = cx.node(h);
        if inner.op != OpCode::Mul {
            continue;
        }
        let (masked, inner_key) = constant_side(cx, inner.a, inner.b)?;
        if inner_key != key {
            continue;
        }
        let input = cx.node(masked);
        if input.op != OpCode::Xor {
            continue;
        }
        let (source, input_key) = constant_side(cx, input.a, input.b)?;
        if input_key == key {
            return Some((key, source));
        }
    }
    None
}
fn bounded(cx: &Context, id: u32, bits: u8, work: &mut usize) -> bool {
    if *work == 0 {
        return false;
    }
    *work -= 1;
    let node = cx.node(id);
    if node.width <= u16::from(bits) {
        return true;
    }
    if let Some(value) = cx.const_val(id).and_then(|v| v.to_u64()) {
        return value >> bits == 0;
    }
    if cx
        .declared_at(id)
        .is_some_and(|k| k.leading_known_zeros() >= u32::from(node.width - u16::from(bits)))
    {
        return true;
    }
    match node.op {
        OpCode::Zext => bounded(cx, node.a, bits, work),
        OpCode::And => constant_side(cx, node.a, node.b).is_some_and(|(_, mask)| mask >> bits == 0),
        OpCode::Select => bounded(cx, node.b, bits, work) && bounded(cx, node.c, bits, work),
        _ => false,
    }
}
fn source_equals(cx: &mut Context, source: u32, candidate: u64) -> Result<u32, Error> {
    let node = cx.node(source);
    let input = if node.op == OpCode::Zext {
        node.a
    } else {
        source
    };
    let width = cx.width_of(input);
    if width.bits() < 64 && candidate >> width.bits() != 0 {
        return cx.mk_const(&BitVec::zero(Width::W1));
    }
    let value = cx.mk_const(&BitVec::from_u64(width, candidate).unwrap())?;
    cx.c_cmp(crate::CmpOp::Eq, input, value)
}

fn fold_boolean_complements(cx: &mut Context, id: u32) -> Result<u32, Error> {
    let node = cx.node(id);
    if node.width != 1 || !matches!(node.op, OpCode::And | OpCode::Or | OpCode::Xor) {
        return Ok(id);
    }
    let a = cx.node(node.a);
    let b = cx.node(node.b);
    let complements = (a.op == OpCode::Not && a.a == node.b)
        || (b.op == OpCode::Not && b.a == node.a)
        || (matches!(
            (a.op, b.op),
            (OpCode::Eq, OpCode::Ne) | (OpCode::Ne, OpCode::Eq)
        ) && a.a == b.a
            && a.b == b.b);
    if complements {
        cx.mk_const(&BitVec::from_u64(Width::W1, u64::from(node.op != OpCode::And)).unwrap())
    } else {
        Ok(id)
    }
}

#[cfg(test)]
mod tests;
