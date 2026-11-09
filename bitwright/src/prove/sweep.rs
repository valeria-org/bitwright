//! SAT sweeping ([`Config::sweeping`](super::Config::sweeping)): nodes of the circuit that
//! compute one function are found by simulation, proved equivalent one pair at a time, and
//! their equivalence handed to the search as clauses.
//!
//! Two circuits for one function often share far more than their outputs: a prefix adder and
//! the adder `x + y` blasts to have the same carries, written differently, and an MBA
//! rewriting keeps most of its operands' bits. A search over the miter alone has to
//! rediscover each of those equivalences inside one large refutation. Proved separately and
//! in order, from the inputs up, each is a small question once the ones below it are known:
//! bit `i` of a sum reads only bits below it, so for arithmetic this order is low bits first.
//! A circuit with nothing inside in common, such as the shift-and-xor addition loop against
//! `x + y`, whose carries no single node holds, gains little or loses: the simulation shows
//! which kind a question is before any proof is tried ([`Shape::worth_proving`]), and the
//! others are left to the search as they are.
//!
//! The circuit is simulated on bit-parallel assignments chosen per word of the question, not
//! per bit: boundary values, random, sparse and dense values, runs of ones, and values
//! related to the word before (its complement, its negation, itself), so that the rare
//! events of arithmetic happen (`x + -x` carries from its lowest one to the top, which
//! random bits almost never do). Nodes whose values agree everywhere, or disagree everywhere, are
//! candidates, the earliest of a class its representative (the constant false is one). Each
//! candidate is proved against its representative by a separate solver holding only the
//! circuit's clauses, under assumptions: `a ∧ ¬b`, then `¬a ∧ b`. Without the question's
//! assertion, a pair that is not equivalent is refuted at once, and its counterexample, with
//! its neighbours one input bit away, splits the classes; within the question's solver it
//! could only be refuted by deciding the whole question. A pair undecided within
//! [`PAIR_CONFLICTS`] is left alone.
//!
//! The equivalences go to the question's solver as clauses. The sweep's solver holds a
//! subset of the question's clauses, in the same variables, so every clause it learned is a
//! reverse-unit-propagation consequence there too: with a certificate, its additions are
//! logged ahead of the equivalences, and the certificate still checks independently.

use std::collections::HashMap;

use super::aig::{Aig, Cnf, L};
use super::sat::{Answer, Limits, Lit, Solver};

/// The simulation words a sweep starts with (64 assignments each).
const WORDS: usize = 8;

/// The most conflicts one proof of a pair may take.
pub(super) const PAIR_CONFLICTS: u64 = 300;

/// The most simulation words kept, over all candidates: the counterexamples that refine the
/// classes stop there, and so does the sweep (a pair refuted without refining the classes
/// would be tried again, and each refutation costs a model of the whole circuit).
const MAX_SIGNATURE_WORDS: usize = 1 << 22;

/// Candidate pairs a sweep may see told apart before the first merge, and then per merge:
/// beyond them the simulation is missing too much and the sweep stops.
const GRACE: u64 = 64;
const SEPARATED_PER_MERGE: u64 = 4;

/// The largest circuit swept (simulation keeps a word per node and word).
const MAX_NODES: usize = 1 << 20;

/// The circuit of a question, as its preparation hands it to the sweep.
pub(super) struct Pending {
    pub(super) aig: Aig,
    pub(super) roots: Vec<L>,
    /// The bits of each word of the question (symbol), low bit first.
    pub(super) words: Vec<Vec<L>>,
    /// The bits of the two sides, when the question is an equality.
    pub(super) sides: Option<(Vec<L>, Vec<L>)>,
    pub(super) xor3: bool,
    pub(super) certificate: bool,
}

/// What a sweep did and cost.
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
pub(super) struct Work {
    /// Simulated, and its candidate pairs proved.
    pub(super) ran: bool,
    /// Simulated, and judged not worth proving ([`Shape::worth_proving`]).
    pub(super) skipped: bool,
    /// The classes the first simulation found joining the two sides.
    pub(super) crossings: u64,
    pub(super) merged: u64,
    pub(super) separated: u64,
    pub(super) undecided: u64,
    pub(super) conflicts: u64,
    pub(super) decisions: u64,
    pub(super) propagations: u64,
    pub(super) lemmas: u64,
}

/// A pair's fate.
enum Pair {
    /// Proved: the clauses that say so.
    Merged(Vec<Vec<Lit>>),
    /// A model of the circuit where the two differ.
    Separated(Vec<bool>),
    Undecided,
}

/// Simulation signatures, normalized so that the first assignment (all inputs 0) gives 0: a
/// column of words per simulation word, one per candidate, and each candidate's hash of its
/// words so far, so a new word costs one pass over the candidates.
struct Sigs {
    cols: Vec<Vec<u64>>,
    keys: Vec<u64>,
}

impl Sigs {
    fn new(candidates: usize) -> Sigs {
        Sigs {
            cols: Vec::new(),
            keys: vec![0xcbf2_9ce4_8422_2325; candidates],
        }
    }

    fn words(&self) -> usize {
        self.cols.len()
    }

    fn key(&self, c: usize) -> u64 {
        self.keys[c]
    }

    fn same(&self, a: usize, b: usize) -> bool {
        self.keys[a] == self.keys[b] && self.cols.iter().all(|col| col[a] == col[b])
    }

    /// Adds a word per candidate.
    fn push(&mut self, word: impl Fn(usize) -> u64) {
        let col: Vec<u64> = (0..self.keys.len()).map(word).collect();
        for (k, &w) in self.keys.iter_mut().zip(&col) {
            *k = (*k ^ w).wrapping_mul(0x0100_0000_01b3).rotate_left(29);
        }
        self.cols.push(col);
    }
}

fn mix(z: u64) -> u64 {
    let mut z = z.wrapping_add(0x9e37_79b9_7f4a_7c15);
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The value of word `s` (of `bits` bits, chunk `chunk` of 64 for a wider one) in assignment
/// `lane` of batch `b`, given the previous word's value there (`prev`). Assignment 0 is all
/// zeros (the normalization reads it) and assignment 1 all ones; batch 0 is a grid of the
/// boundary values. The other assignments each take one mode for all the words: random,
/// sparse or dense values, runs of ones, or a first value and each next word related to the
/// one before: its negation (the first value with its lowest one at a chosen bit, so that a
/// sum of the two carries from there to the top), the same with the run broken at a chosen
/// bit, its complement, or itself.
fn value(b: usize, lane: usize, s: usize, chunk: usize, bits: u32, prev: Option<u64>) -> u64 {
    let mask = if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let r = |salt: u64| {
        mix((b as u64) << 48 ^ (lane as u64) << 32 ^ (s as u64) << 12 ^ (chunk as u64) << 4 ^ salt)
    };
    // Shared by the words of the assignment.
    let lane_r = |salt: u64| mix((b as u64) << 48 ^ (lane as u64) << 32 ^ 0x6c61_6e65 ^ salt);
    let at = lane_r(1) % u64::from(bits.max(1));
    let v = match (b, lane) {
        (0, 0) => 0,
        (0, 1) => u64::MAX,
        (0, _) => {
            let sign = if bits >= 64 {
                1 << 63
            } else {
                1u64 << (bits - 1)
            };
            let boundary = [0, 1, u64::MAX, sign, mask >> 1, sign | 1];
            let digit = (lane / 6usize.pow((s % 3) as u32)) % 6;
            boundary[digit]
        }
        _ => match (lane_r(0) % 9, prev) {
            (0, _) => r(1),
            (1, _) => r(1) & r(2),
            (2, _) => r(1) | r(2),
            (3, _) => {
                let len = r(2) % 65;
                let run = if len == 64 {
                    u64::MAX
                } else {
                    (1u64 << len) - 1
                };
                run << (r(1) % 64)
            }
            (4 | 5, None) => (r(1) | 1) << at,
            (4, Some(p)) => p.wrapping_neg(),
            (5, Some(p)) => p.wrapping_neg() ^ (1 << (lane_r(2) % u64::from(bits.max(1)))),
            (6, Some(p)) => !p,
            (7, Some(p)) => p,
            _ => r(1).wrapping_sub(r(2) >> (r(3) % 64)),
        },
    };
    v & mask
}

/// The input words of simulation batch `b`, by input ordinal (`ordinal[node]`): each word of
/// the question takes [`value`]s, transposed into its bits' inputs, and an input of no word
/// a random word.
fn batch(b: usize, words: &[Vec<L>], ordinal: &[Option<u32>], inputs: usize) -> Vec<u64> {
    let mut out: Vec<u64> = (0..inputs)
        .map(|k| {
            let z = mix((b as u64) << 40 ^ k as u64 ^ 0x5157);
            if b == 0 { (z & !0b11) | 0b10 } else { z }
        })
        .collect();
    let mut prev: Vec<u64> = Vec::new();
    for (s, bits) in words.iter().enumerate() {
        let w = bits.len();
        let mut lanes = vec![0u64; 64];
        for chunk in 0..w.div_ceil(64) {
            let width = (w - chunk * 64).min(64) as u32;
            for (lane, v) in lanes.iter_mut().enumerate() {
                let p = (chunk == 0 && s > 0)
                    .then(|| prev.get(lane).copied())
                    .flatten();
                *v = value(b, lane, s, chunk, width, p);
            }
            if chunk == 0 {
                prev = lanes.clone();
            }
            for t in 0..width as usize {
                let l = bits[chunk * 64 + t];
                let Some(k) = ordinal[(l >> 1) as usize] else {
                    continue;
                };
                let mut word = 0u64;
                for (lane, v) in lanes.iter().enumerate() {
                    word |= ((v >> t) & 1) << lane;
                }
                out[k as usize] = if l & 1 == 1 { !word } else { word };
            }
        }
    }
    out
}

/// Sweeps the circuit of `p`, whose question's clauses `cnf` encoded into `main`, within
/// `limits`; the equivalences proved are added to `main`.
pub(super) fn sweep(p: &Pending, cnf: &Cnf, main: &mut Solver, limits: Limits) -> Work {
    let mut work = Work::default();
    let n = p.aig.len();
    if n > MAX_NODES || limits.conflicts == 0 || limits.propagations == 0 {
        return work;
    }
    // Candidates: the constant, then every node with a variable, in creation order (operands
    // before their gates). The sweep's own encoding gives every node the variable the
    // question's does (checked when it is made).
    let lit = |node: usize| cnf.mapped_lit((node as u32) << 1);
    let cand: Vec<usize> = core::iter::once(0)
        .chain((1..n).filter(|&i| lit(i).is_some()))
        .collect();
    let inputs: Vec<usize> = (0..n).filter(|&i| p.aig.is_input(i)).collect();
    let mut ordinal = vec![None; n];
    for (k, &i) in inputs.iter().enumerate() {
        ordinal[i] = Some(k as u32);
    }

    let mut sigs = Sigs::new(cand.len());
    let mut pol = vec![false; cand.len()];
    for b in 0..WORDS {
        let input = batch(b, &p.words, &ordinal, inputs.len());
        let vals = p.aig.eval_words(|k| input[k as usize]);
        if b == 0 {
            for (c, &i) in cand.iter().enumerate() {
                pol[c] = vals[i] & 1 == 1;
            }
        }
        sigs.push(|c| {
            let v = vals[cand[c]];
            if pol[c] { !v } else { v }
        });
    }
    let shape = shape(p, &cand, &sigs);
    work.crossings = shape.cross as u64;
    if !shape.worth_proving() {
        work.skipped = true;
        return work;
    }
    let mut s = Solver::new();
    if p.certificate {
        s.log_proof();
    }
    let scnf = Cnf::encode_with_xor3(&p.aig, &p.roots, &mut s, false, p.xor3);
    if !scnf.same_variables(cnf) {
        return work;
    }
    work.ran = true;

    let (c0, p0) = (s.conflicts, s.propagations);
    let (d0, l0) = (s.decisions, s.lemmas);
    let mut reps: Vec<usize> = Vec::new();
    let mut classes: HashMap<u64, Vec<usize>> = HashMap::new();
    let mut eqs: Vec<Vec<Lit>> = Vec::new();
    let mut refinements = 0u64;
    'candidates: for c in 0..cand.len() {
        loop {
            let (spent_c, spent_p) = (s.conflicts - c0, s.propagations - p0);
            if spent_c >= limits.conflicts || spent_p >= limits.propagations {
                break 'candidates;
            }
            let key = sigs.key(c);
            let rep = classes
                .get(&key)
                .and_then(|rs| rs.iter().copied().find(|&r| sigs.same(r, c)));
            let Some(r) = rep else {
                classes.entry(key).or_default().push(c);
                reps.push(c);
                break;
            };
            let pair = Limits {
                conflicts: PAIR_CONFLICTS.min(limits.conflicts - spent_c),
                propagations: limits.propagations - spent_p,
            };
            // `cand[c]` is `cand[r]`, complemented when their normalizations differ.
            let flip = pol[c] != pol[r];
            let Some(b) = lit(cand[c]) else { break };
            let b = if flip { !b } else { b };
            let fate = match (r, lit(cand[r])) {
                // The constant false: `b` is false.
                (0, _) => prove_clause(&mut s, &[!b], pair),
                (_, Some(a)) => match prove_clause(&mut s, &[!a, b], pair) {
                    Pair::Merged(mut first) => match prove_clause(&mut s, &[a, !b], pair) {
                        Pair::Merged(second) => {
                            first.extend(second);
                            Pair::Merged(first)
                        }
                        other => other,
                    },
                    other => other,
                },
                (_, None) => Pair::Undecided,
            };
            match fate {
                Pair::Merged(clauses) => {
                    work.merged += 1;
                    eqs.extend(clauses);
                    break;
                }
                Pair::Undecided => {
                    work.undecided += 1;
                    break;
                }
                Pair::Separated(model) => {
                    work.separated += 1;
                    // Simulation that keeps missing what tells candidates apart costs a model
                    // of the circuit per pair: past a few per merge, the sweep stops.
                    if work.separated > GRACE + SEPARATED_PER_MERGE * work.merged
                        || (sigs.words() + 1) * cand.len() > MAX_SIGNATURE_WORDS
                        || inputs.is_empty()
                    {
                        break 'candidates;
                    }
                    refinements += 1;
                    // The counterexample, and in each other assignment of the word one input
                    // bit flipped.
                    let base: Vec<bool> = inputs
                        .iter()
                        .map(|&i| scnf.value((i as u32) << 1, &model))
                        .collect();
                    let salt = mix(refinements);
                    let vals = p.aig.eval_words(|k| {
                        let mut word = if base[k as usize] { u64::MAX } else { 0 };
                        for lane in 1..64u64 {
                            if mix(salt ^ lane) % inputs.len() as u64 == u64::from(k) {
                                word ^= 1 << lane;
                            }
                        }
                        word
                    });
                    sigs.push(|c| {
                        let v = vals[cand[c]];
                        if pol[c] { !v } else { v }
                    });
                    classes.clear();
                    for &r in &reps {
                        classes.entry(sigs.key(r)).or_default().push(r);
                    }
                }
            }
        }
    }
    work.conflicts = s.conflicts - c0;
    work.decisions = s.decisions - d0;
    work.propagations = s.propagations - p0;
    work.lemmas = s.lemmas - l0;
    if !eqs.is_empty() {
        main.import(s.take_proof().unwrap_or_default(), &eqs);
    }
    work
}

/// What the first simulation shows of the candidates, before any proof.
#[derive(Debug, Default, Clone, Copy)]
struct Shape {
    /// Candidates in the cone of one side only (of all of them, without sides).
    private: usize,
    /// Classes other than the constants' holding candidates private to both sides (without
    /// sides: holding two candidates or more).
    cross: usize,
    /// Candidates that look constant.
    constant: usize,
}

/// The candidates private to a side per class joining the sides, at most, for a sweep to be
/// worth its proofs.
const PRIVATE_PER_CROSSING: usize = 10;

/// The fewest classes joining the sides worth proving.
const MIN_CROSSINGS: usize = 4;

impl Shape {
    /// Whether the merges the simulation promises are worth proving: at least
    /// [`MIN_CROSSINGS`] classes joining the two sides, one per [`PRIVATE_PER_CROSSING`]
    /// candidates private to a side or fewer. Measured on adders, bit counts, MBA rewritings
    /// and products: the sweep paid wherever there was one class per 8 or fewer (prefix
    /// adders 0.13, MBA rewritings of `x - y` 0.14, the SWAR count 0.27 to 0.42), and did not
    /// at one per 10 or more (the shift-and-xor addition loop 0.06 at 16 bits, products 0.02 to
    /// 0.03, where the proofs of hard pairs cost more than they save).
    fn worth_proving(&self) -> bool {
        self.cross >= MIN_CROSSINGS && self.cross * PRIVATE_PER_CROSSING >= self.private
    }
}

/// The [`Shape`] of the candidates `cand` under the signatures `sigs`.
fn shape(p: &Pending, cand: &[usize], sigs: &Sigs) -> Shape {
    let n = p.aig.len();
    // Bit 1: in the first side's cone; bit 2: in the second's.
    let mut side = vec![0u8; n];
    if let Some((a, b)) = &p.sides {
        for (bit, roots) in [(1u8, a), (2u8, b)] {
            let mut stack: Vec<usize> = roots.iter().map(|&l| (l >> 1) as usize).collect();
            while let Some(i) = stack.pop() {
                if side[i] & bit != 0 {
                    continue;
                }
                side[i] |= bit;
                if let Some((x, y)) = p.aig.gate(i) {
                    stack.push((x >> 1) as usize);
                    stack.push((y >> 1) as usize);
                }
            }
        }
    } else {
        side.iter_mut().for_each(|s| *s = 3);
    }
    let private = |c: usize| matches!(side[cand[c]], 1 | 2);
    let mut classes: HashMap<u64, Vec<usize>> = HashMap::new();
    for c in 1..cand.len() {
        classes.entry(sigs.key(c)).or_default().push(c);
    }
    let mut shape = Shape {
        private: (1..cand.len())
            .filter(|&c| if p.sides.is_some() { private(c) } else { true })
            .count(),
        ..Shape::default()
    };
    for members in classes.values() {
        // Classes share keys only by collision; one key, one class is close enough to count.
        if sigs.same(members[0], 0) {
            shape.constant += members.len();
            continue;
        }
        let crossing = if p.sides.is_some() {
            members.iter().any(|&c| side[cand[c]] == 1)
                && members.iter().any(|&c| side[cand[c]] == 2)
        } else {
            members.len() > 1
        };
        shape.cross += usize::from(crossing);
    }
    shape
}

/// Whether `clause` follows from the circuit's clauses in `s`: its negation is assumed, and
/// when that is contradictory the clause is added (checked by unit propagation, logged).
fn prove_clause(s: &mut Solver, clause: &[Lit], limits: Limits) -> Pair {
    let assumptions: Vec<Lit> = clause.iter().map(|&l| !l).collect();
    match s.solve_assuming(&assumptions, limits) {
        Answer::Unsat if !s.is_unsat() => {
            let rejected = s.rejected_lemmas;
            if s.add_rup_clause(clause) && s.rejected_lemmas == rejected {
                Pair::Merged(vec![clause.to_vec()])
            } else {
                Pair::Undecided
            }
        }
        Answer::Sat(model) => Pair::Separated(model),
        _ => Pair::Undecided,
    }
}
