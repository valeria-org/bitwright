//! Bounded joint output supersets above expensive Boolean predicates.
//!
//! Unavailable predicates become independent Boolean inputs, shared by expression identity.
//! Enumerating their small Boolean support preserves correlations between output roots without
//! solving the predicates themselves. Every original output tuple satisfying the premises is
//! included. A returned tuple need not have an original-symbol witness, and this analysis
//! establishes neither reachability nor completeness of an external graph.
//!
//! ```
//! use bitwright::{Context, Width};
//! use bitwright::prove::domain::{Analysis, Limits, analyze};
//! let mut cx = Context::new();
//! let p = cx.symbol("p", Width::W1)?;
//! let a = cx.constant_u64(Width::W64, 7)?;
//! let b = cx.constant_u64(Width::W64, 11)?;
//! let target = cx.select(p, a, b)?;
//! let flag = cx.zext(p, Width::W32)?;
//! let Analysis::Superset(domain) = analyze(&mut cx, &[target, flag], &[], Limits::default())?
//! else { panic!("small joint domain") };
//! assert_eq!(domain.tuples().len(), 2);
//! // domain.coverage(&mut cx) builds the original scoped coverage predicate,
//! // which can be checked independently through Question::valid.
//! # Ok::<(), bitwright::Error>(())
//! ```

use super::{aig::Aig, cuts::Probe};
use crate::{BitVec, Context, Error, Expr, WidthError, hash::IdMap};

/// Work allowances for [`analyze`]. No SAT search or original-input enumeration is used.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Limits {
    /// Expression nodes examined, capped at 256 to bound recursive stack depth.
    pub visits: usize,
    /// Circuit nodes, including the constant and abandoned intermediate gates.
    /// Checked after each bounded operator; construction can overshoot by one operator.
    pub nodes: usize,
    /// Weighted bit-operation work during construction, capped at 16,384.
    pub construction_work: usize,
    /// Circuit evaluations plus output-bit/tuple work for complete abstract enumeration.
    pub enumeration_work: usize,
    /// Live Boolean inputs to enumerate, with an additional hard ceiling of 20.
    pub inputs: usize,
    /// Distinct tuples retained. An overflowing list is discarded, never returned as complete.
    pub tuples: usize,
    /// Sum of output widths, with an additional hard ceiling of 4,096 bits.
    pub output_bits: usize,
}

impl Default for Limits {
    fn default() -> Self {
        Self {
            visits: 256,
            nodes: 4096,
            construction_work: 16_384,
            enumeration_work: 1_048_576,
            inputs: 12,
            tuples: 256,
            output_bits: 4096,
        }
    }
}

/// A complete overapproximation was unavailable. No partial tuple list is supplied.
#[derive(Clone, Debug, PartialEq, Eq)]
pub enum Stop {
    /// More than 64 outputs or 64 premises were requested.
    TooManyRoots,
    /// The sum of output widths exceeded the allowance.
    OutputBits,
    /// An output could not be expressed over the bounded Boolean cut.
    UnavailableOutput(usize),
    /// Circuit construction exceeded the node allowance.
    Nodes(usize),
    /// The number of live Boolean inputs exceeded the allowance.
    Inputs(usize),
    /// Complete abstract enumeration exceeded the work allowance.
    EnumerationWork,
    /// The distinct tuple count exceeded the allowance.
    Tuples,
}

/// The complete abstract result or an explicit resource/representation stop.
#[derive(Clone, Debug)]
pub enum Analysis {
    /// A sound joint output superset for the original expressions and premises.
    Superset(TupleDomain),
    /// The requested domain was not recovered within the limits.
    Unknown(Stop),
}

/// Construction and complete abstract enumeration counts, not original-input samples.
#[derive(Clone, Copy, Debug, PartialEq, Eq)]
pub struct Stats {
    /// Constructed circuit nodes, including dead intermediates.
    pub nodes: usize,
    /// Boolean inputs live in the outputs or premises.
    pub inputs: usize,
    /// Abstract Boolean assignments evaluated, including those rejected by premises.
    pub assignments: usize,
}

/// Joint values in output-root order, scoped to the original premises and symbol declarations.
///
/// Fields are private: construction requires complete abstract enumeration. Tuples are ordered
/// by first occurrence in that enumeration. Both impossible and reachable tuples can occur.
/// Reanalyze when declarations, expressions, or premises change; this is not a global fact.
#[derive(Clone, Debug)]
pub struct TupleDomain {
    outputs: Vec<Expr>,
    premises: Vec<Expr>,
    tuples: Vec<Vec<BitVec>>,
    stats: Stats,
}

impl TupleDomain {
    /// Original output roots, in tuple field order.
    pub fn outputs(&self) -> &[Expr] {
        &self.outputs
    }

    /// Original Boolean premises. All must hold for the domain guarantee.
    pub fn premises(&self) -> &[Expr] {
        &self.premises
    }

    /// Every tuple in the recovered superset. An empty list means the premises are infeasible
    /// in the overapproximation, not that a resource limit interrupted enumeration.
    pub fn tuples(&self) -> &[Vec<BitVec>] {
        &self.tuples
    }

    /// Bounded construction and enumeration counts.
    pub fn stats(&self) -> Stats {
        self.stats
    }

    /// Build `premises => OR(tuple equalities)` over the original expressions.
    ///
    /// This can be independently verified with a native prover certificate. It does not
    /// prove any individual tuple reachable or assert that an external graph represents it.
    pub fn coverage(&self, cx: &mut Context) -> Result<Expr, Error> {
        for &root in self.outputs.iter().chain(&self.premises) {
            cx.id(root)?;
        }
        let mut covered = cx.zero(crate::Width::W1)?;
        for tuple in &self.tuples {
            let mut equal = cx.one(crate::Width::W1)?;
            for (&output, value) in self.outputs.iter().zip(tuple) {
                let value = cx.constant(value)?;
                let field = cx.eq(output, value)?;
                equal = cx.and(equal, field)?;
            }
            covered = cx.or(covered, equal)?;
        }
        for &premise in &self.premises {
            let absent = cx.not(premise)?;
            covered = cx.or(absent, covered)?;
        }
        Ok(covered)
    }
}

/// Recover a bounded joint output superset under explicit Boolean premises.
///
/// All roots are compiled together, so repeated predicates and their casts retain one
/// Boolean value. Unsupported wide outputs fail explicitly; unsupported Boolean predicates
/// are safely overapproximated. Premises are compiled in the same shared graph. Partial
/// known bits/ranges can be supplied as scoped Boolean predicates, never as global declarations
/// unless globally justified. No returned abstract assignment is an original-symbol model.
/// Single-bit extracts and masks keeping at most eight bits can project unavailable source
/// words without expanding their other bits. Opaque bit projections may admit impossible tuples.
pub fn analyze(
    cx: &mut Context,
    outputs: &[Expr],
    premises: &[Expr],
    limits: Limits,
) -> Result<Analysis, Error> {
    let unknown = |why| Ok(Analysis::Unknown(why));
    if outputs.len() > 64 || premises.len() > 64 {
        return unknown(Stop::TooManyRoots);
    }
    let mut ids = Vec::with_capacity(outputs.len());
    let mut widths = Vec::with_capacity(outputs.len());
    let mut output_bits = 0usize;
    for &output in outputs {
        let id = cx.id(output)?;
        let width = cx.width_of(id);
        output_bits += usize::from(width.bits());
        ids.push(id);
        widths.push(width);
    }
    let mut constraints = Vec::with_capacity(premises.len());
    for &premise in premises {
        let id = cx.id(premise)?;
        if cx.wid(id) != 1 {
            return Err(WidthError::ConditionWidth { bits: cx.wid(id) }.into());
        }
        constraints.push(id);
    }
    if output_bits > limits.output_bits.min(4096) {
        return unknown(Stop::OutputBits);
    }
    let mut probe = Probe::new(
        cx,
        limits.visits,
        limits.nodes,
        limits.construction_work.min(16_384),
    );
    let mut words = Vec::with_capacity(ids.len());
    for (index, &id) in ids.iter().enumerate() {
        let bits = probe.word(id);
        if probe.blaster.g.len() > limits.nodes {
            return unknown(Stop::Nodes(probe.blaster.g.len()));
        }
        let Some(bits) = bits else {
            return unknown(Stop::UnavailableOutput(index));
        };
        words.push(bits);
    }
    let mut conditions = Vec::with_capacity(constraints.len());
    for &id in &constraints {
        // Every Boolean root is representable, at worst by an independent cut input.
        conditions.push(probe.word(id).expect("Boolean cut")[0]);
        if probe.blaster.g.len() > limits.nodes {
            return unknown(Stop::Nodes(probe.blaster.g.len()));
        }
    }
    let graph = &probe.blaster.g;
    if graph.len() > limits.nodes {
        return unknown(Stop::Nodes(graph.len()));
    }
    let live_roots = words
        .iter()
        .flatten()
        .copied()
        .chain(conditions.iter().copied())
        .collect::<Vec<_>>();
    let (support, inputs) = graph.input_support(&live_roots);
    if inputs > limits.inputs.min(20) {
        return unknown(Stop::Inputs(inputs));
    }
    let assignments = 1usize << inputs;
    let batches = assignments.div_ceil(64);
    let per_tuple = output_bits + 8 * outputs.len();
    let Some(work) = (graph.len() + conditions.len())
        .checked_mul(batches)
        .and_then(|n| {
            assignments
                .checked_mul(per_tuple)
                .and_then(|m| n.checked_add(m))
        })
    else {
        return unknown(Stop::EnumerationWork);
    };
    if work > limits.enumeration_work {
        return unknown(Stop::EnumerationWork);
    }
    let mut seen = IdMap::<Vec<BitVec>, ()>::default();
    let mut tuples = Vec::new();
    for base in (0..assignments).step_by(64) {
        let lanes = (assignments - base).min(64);
        let values = graph.eval_assignment_batch(&support, base);
        let mut active = if lanes == 64 {
            u64::MAX
        } else {
            (1u64 << lanes) - 1
        };
        for &condition in &conditions {
            active &= Aig::word(&values, condition);
        }
        while active != 0 {
            let lane = active.trailing_zeros();
            active &= active - 1;
            let tuple = words
                .iter()
                .zip(&widths)
                .map(|(bits, &width)| {
                    let mut limbs = [0u64; 8];
                    for (bit, &literal) in bits.iter().enumerate() {
                        limbs[bit / 64] |=
                            ((Aig::word(&values, literal) >> lane) & 1) << (bit % 64);
                    }
                    BitVec::wrapping_from_limbs(width, &limbs)
                })
                .collect::<Vec<_>>();
            if seen.contains_key(&tuple) {
                continue;
            }
            if tuples.len() == limits.tuples {
                return unknown(Stop::Tuples);
            }
            seen.insert(tuple.clone(), ());
            tuples.push(tuple);
        }
    }
    Ok(Analysis::Superset(TupleDomain {
        outputs: outputs.to_vec(),
        premises: premises.to_vec(),
        tuples,
        stats: Stats {
            nodes: graph.len(),
            inputs,
            assignments,
        },
    }))
}

#[cfg(test)]
mod tests;
