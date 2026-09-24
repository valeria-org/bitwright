//! The native normal-form solver (design §9).
//!
//! One pass over the expression, operands first, gives every node the normal form of the
//! smallest fragment that contains it: a bitwise function of atoms (a truth table per bit
//! class), or a polynomial over masked conjunctions of atoms. Atoms are the variables and every
//! subterm the fragments cannot see through. From the root's normal form, candidate forms are
//! rendered and the cheapest kept; it is certified against the input before it is returned.

mod bits;
mod classes;
mod poly;
mod render;
mod synth;

use std::collections::{HashMap, VecDeque};
use std::sync::Mutex;

use self::bits::{BitOp, Bits};
use self::classes::{Classes, FULL};
use self::poly::{Mono, Poly, Sym};
use self::render::{Builder, Render};
use super::certify::{self, Steps};
use super::expr::{MNode, MOp, MbaExpr};
use super::solve::{Claim, MbaAnswer, MbaBudget, MbaSolver, Verdict};
use crate::engine::CertStats;
use crate::{BitVec, Width};

/// Certificate work is counted in steps of this many node evaluations (see
/// [`NormalFormSolver`]).
const EVALS_PER_STEP: u64 = 32;

/// The largest expansion over classes tried when turning masked symbols back into unmasked
/// ones.
const DECLASS_LIMIT: usize = 256;

/// The most terms of a normal form in which atoms are looked for as their definitions
/// (larger ones are rendered as they are).
const REUSE_TERMS: usize = 64;

/// Runs [`certify::check`] within `work` and charges what it spent.
fn certify_within(a: &MbaExpr, b: &MbaExpr, work: &mut Steps) -> certify::Report {
    use certify::Meter;
    let report = certify::check(a, b, work.left.saturating_mul(EVALS_PER_STEP));
    let spent = report.work.div_ceil(EVALS_PER_STEP).min(work.left);
    let _ = work.charge(spent);
    report
}

/// What the normal-form solver takes on. Every limit is checked before the work it bounds.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
#[non_exhaustive]
pub struct NfOptions {
    /// The most atoms (variables and abstracted subterms), at most 64.
    pub max_atoms: u32,
    /// The most bit classes (distinct bit patterns of the constants read bitwise).
    pub max_classes: u32,
    /// The most monomials in one normal form (a larger sum, product, or bitwise function read
    /// arithmetically is an atom).
    pub max_terms: u32,
    /// The highest degree of a normal form (a product of higher degree is an atom).
    pub max_degree: u32,
    /// The most questions whose answers the solver remembers (0: none). The engine asks the
    /// same question again as the expression around it changes; a remembered answer is the
    /// one solving again would give, so this changes time, never answers.
    pub memo: u32,
    /// Bounded enumerative synthesis: a normal form over at most three atoms is also looked up
    /// in a table of the smallest expressions (up to seven nodes) by its values at fixed probe
    /// points. A hit is a candidate once a certificate proves it equal; one no certificate can
    /// decide is at most a sampled answer (`Claim::Sampled`).
    pub synthesis: bool,
}

impl Default for NfOptions {
    /// 16 atoms, 32 classes, 1024 monomials, degree 32; 1024 answers remembered; synthesis on.
    fn default() -> Self {
        NfOptions {
            max_atoms: 16,
            max_classes: 32,
            max_terms: 1024,
            max_degree: 32,
            memo: 1024,
            synthesis: true,
        }
    }
}

setters!(NfOptions {
    with_max_atoms: max_atoms: u32,
    with_max_classes: max_classes: u32,
    with_max_terms: max_terms: u32,
    with_max_degree: max_degree: u32,
    with_memo: memo: u32,
    with_synthesis: synthesis: bool,
});

/// What the normal-form solver has done (telemetry; never affects answers).
#[derive(Copy, Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct NfStats {
    /// Questions asked.
    pub calls: u64,
    /// Answered with a smaller expression.
    pub simplified: u64,
    /// Answered "no simpler".
    pub no_simpler: u64,
    /// Declined: an input it does not take (see the `declined_*` counters).
    pub unsupported: u64,
    /// Out of budget.
    pub exhausted: u64,
    /// Normal forms reached: linear MBA (one bit class, degree at most 1)...
    pub linear: u64,
    /// ...semi-linear (several bit classes, degree at most 1)...
    pub semilinear: u64,
    /// ...polynomial (a product of two non-constants survives)...
    pub polynomial: u64,
    /// ...and with atoms beyond the variables.
    pub abstracted: u64,
    /// Atoms created for subterms (beyond the variables).
    pub atoms: u64,
    /// Candidate forms rendered.
    pub candidates: u64,
    /// Answers returned with a certificate the solver ran (`Claim::Proved`).
    pub proved: u64,
    /// Answers returned on agreement at the refutation sample only (`Claim::Sampled`).
    pub sampled: u64,
    /// The self-check certificates.
    pub certificates: CertStats,
    /// Declined: several widths outside casts.
    pub declined_widths: u64,
    /// Declined: over `max_atoms`.
    pub declined_atoms: u64,
    /// Declined: over `max_classes`.
    pub declined_classes: u64,
    /// Sums, products or bitwise functions made atoms: over `max_terms` or `max_degree`, or a
    /// bitwise function of more than 12 atoms.
    pub declined_terms: u64,
    /// Null parts of normal forms dropped, each proved zero by a certificate.
    pub null_parts: u64,
    /// Questions whose bitwise operations with constants on bits the facts know were read as
    /// arithmetic before the normal form (`x·−100 | 1` as `x·−100 + 1`)...
    pub lowered: u64,
    /// ...and bitwise operations with a constant read so inside it: the constant reads only low
    /// bits of the other operand's polynomial that are known (`−2·(x & 1) | 1` is
    /// `1 − 2·(x & 1)`).
    pub known_bits: u64,
    /// Normal forms also rendered with an atom standing for its definition where that appears
    /// arithmetically (`p + (y & p)` shares `p`).
    pub reused: u64,
    /// Declined: a candidate the self-check refuted (a bug; never expected).
    pub declined_internal: u64,
    /// Questions answered from the memo (see [`NfOptions::memo`]); also counted by their
    /// answer above, but not in the work counters.
    pub memo_hits: u64,
    /// Synthesis (see [`NfOptions::synthesis`]): normal forms looked up...
    pub synth_lookups: u64,
    /// ...hits cheaper than every other candidate...
    pub synth_hits: u64,
    /// ...of which proved equal by a certificate...
    pub synth_proved: u64,
    /// ...refuted (values that agree at the probes only)...
    pub synth_refuted: u64,
    /// ...or undecided (no certificate fits)...
    pub synth_unproved: u64,
    /// ...and answers returned on an undecided hit, checked at the refutation sample only.
    pub synth_sampled: u64,
}

/// The native solver for linear, semi-linear and polynomial MBA, from exact normal forms at
/// full width; other subterms are atoms. A normal form over at most three atoms is also
/// looked up in a table of small expressions ([`NfOptions::synthesis`]). Every answer is
/// certified against its input by bitwright's own certificates before it is returned
/// (`Claim::Proved`), or, when no certificate fits, checked at the refutation sample
/// (`Claim::Sampled`, which the evidence gate re-checks): exact by construction, except a
/// table hit no certificate could decide. Work is counted in [`MbaBudget::steps`]: one step
/// per node visited, table word combined, monomial product, term or table entry rendered, and
/// one per 32 node evaluations of a certificate. Answers are deterministic; recent ones are
/// remembered ([`NfOptions::memo`]).
///
/// ```
/// use bitwright::mba::{MOp, MbaAnswer, MbaBudget, MbaExpr, MbaSolver, NormalFormSolver};
/// use bitwright::{BitVec, Width};
///
/// // (x ^ 0x10) + 2·(x & 0x10) is x + 0x10.
/// let w = Width::W32;
/// let mut m = MbaExpr::new(vec![w]);
/// let x = m.push(MOp::Var(0), &[])?;
/// let k = m.push(MOp::Const(BitVec::from_u64(w, 0x10).unwrap()), &[])?;
/// let a = m.push(MOp::Xor, &[x, k])?;
/// let b = m.push(MOp::And, &[x, k])?;
/// let t = m.push(MOp::Shl(1), &[b])?;
/// m.push(MOp::Add, &[a, t])?;
/// let solver = NormalFormSolver::default();
/// let MbaAnswer::Simplified { expr, .. } = solver.solve(&m, &MbaBudget::default()) else {
///     panic!("not simplified");
/// };
/// assert_eq!(expr.nodes().len(), 3); // x, 0x10, and their sum
/// assert_eq!(solver.stats().semilinear, 1);
/// # Ok::<(), bitwright::mba::MbaError>(())
/// ```
#[derive(Debug)]
pub struct NormalFormSolver {
    opts: NfOptions,
    id: String,
    stats: Mutex<NfStats>,
    memo: Mutex<Memo>,
}

/// A remembered question: its content hash and budget.
type MemoKey = ([u64; 2], MbaBudget);

/// Answers by question and budget, oldest forgotten first. An entry keeps its question, which
/// must equal the one asked (a hash collision is a miss, never someone else's answer).
#[derive(Debug, Default)]
struct Memo {
    answers: HashMap<MemoKey, (MbaExpr, MbaAnswer)>,
    order: VecDeque<MemoKey>,
}

impl Memo {
    fn get(&self, key: &MemoKey, p: &MbaExpr) -> Option<MbaAnswer> {
        let (q, a) = self.answers.get(key)?;
        (q == p).then(|| a.clone())
    }

    fn put(&mut self, capacity: usize, key: MemoKey, p: &MbaExpr, a: &MbaAnswer) {
        if capacity == 0 {
            return;
        }
        if self.answers.insert(key, (p.clone(), a.clone())).is_none() {
            self.order.push_back(key);
        }
        while self.answers.len() > capacity {
            let Some(old) = self.order.pop_front() else {
                break;
            };
            self.answers.remove(&old);
        }
    }
}

impl Default for NormalFormSolver {
    fn default() -> Self {
        NormalFormSolver::new(NfOptions::default())
    }
}

impl NormalFormSolver {
    /// A solver with these options.
    pub fn new(opts: NfOptions) -> NormalFormSolver {
        let id = format!(
            "bitwright.nf.v3;atoms={};classes={};terms={};degree={};synth={}",
            opts.max_atoms,
            opts.max_classes,
            opts.max_terms,
            opts.max_degree,
            if opts.synthesis { synth::MAX_SIZE } else { 0 }
        );
        NormalFormSolver {
            opts,
            id,
            stats: Mutex::new(NfStats::default()),
            memo: Mutex::new(Memo::default()),
        }
    }

    /// Its options.
    pub fn options(&self) -> NfOptions {
        self.opts
    }

    /// What it has done so far.
    pub fn stats(&self) -> NfStats {
        self.stats.lock().map_or_else(|e| *e.into_inner(), |g| *g)
    }

    fn count(&self, f: impl FnOnce(&mut NfStats)) {
        if let Ok(mut s) = self.stats.lock() {
            f(&mut s);
        }
    }
}

impl MbaSolver for NormalFormSolver {
    fn id(&self) -> &str {
        &self.id
    }

    /// Yes: polynomials are normal forms too.
    fn polynomial_fragments(&self) -> bool {
        true
    }

    fn solve(&self, p: &MbaExpr, budget: &MbaBudget) -> MbaAnswer {
        let mut tally = NfStats {
            calls: 1,
            ..NfStats::default()
        };
        let key = (p.key(), *budget);
        let remembered = self.memo.lock().ok().and_then(|m| m.get(&key, p));
        let answer = match remembered {
            Some(a) => {
                tally.memo_hits += 1;
                a
            }
            None => {
                let a = solve(p, &self.opts, budget, &mut tally);
                if let Ok(mut m) = self.memo.lock() {
                    m.put(self.opts.memo as usize, key, p, &a);
                }
                a
            }
        };
        match &answer {
            MbaAnswer::Simplified { claim, .. } => {
                tally.simplified += 1;
                match claim {
                    Claim::Proved => tally.proved += 1,
                    Claim::Sampled => tally.sampled += 1,
                    // Asked without evidence: unchecked here, the caller proves it.
                    _ => {}
                }
            }
            MbaAnswer::NoSimpler => tally.no_simpler += 1,
            MbaAnswer::Unsupported(_) => tally.unsupported += 1,
            MbaAnswer::Exhausted => tally.exhausted += 1,
        }
        self.count(|s| add_stats(s, &tally));
        answer
    }
}

fn add_stats(s: &mut NfStats, t: &NfStats) {
    s.calls += t.calls;
    s.simplified += t.simplified;
    s.no_simpler += t.no_simpler;
    s.unsupported += t.unsupported;
    s.exhausted += t.exhausted;
    s.linear += t.linear;
    s.semilinear += t.semilinear;
    s.polynomial += t.polynomial;
    s.abstracted += t.abstracted;
    s.atoms += t.atoms;
    s.candidates += t.candidates;
    s.proved += t.proved;
    s.sampled += t.sampled;
    let c = &mut s.certificates;
    let d = &t.certificates;
    c.calls += d.calls;
    c.proved += d.proved;
    c.refuted += d.refuted;
    c.unknown += d.unknown;
    c.signature += d.signature;
    c.single_bit += d.single_bit;
    c.sparse += d.sparse;
    c.grid += d.grid;
    c.exhaustive += d.exhaustive;
    c.compositional += d.compositional;
    c.split += d.split;
    c.known_bits += d.known_bits;
    c.points += d.points;
    c.over_budget += d.over_budget;
    c.internal += d.internal;
    s.declined_widths += t.declined_widths;
    s.declined_atoms += t.declined_atoms;
    s.declined_classes += t.declined_classes;
    s.declined_terms += t.declined_terms;
    s.null_parts += t.null_parts;
    s.lowered += t.lowered;
    s.known_bits += t.known_bits;
    s.reused += t.reused;
    s.declined_internal += t.declined_internal;
    s.memo_hits += t.memo_hits;
    s.synth_lookups += t.synth_lookups;
    s.synth_hits += t.synth_hits;
    s.synth_proved += t.synth_proved;
    s.synth_refuted += t.synth_refuted;
    s.synth_unproved += t.synth_unproved;
    s.synth_sampled += t.synth_sampled;
}

/// Adds a rendering's synthesis counts.
fn add_synth(s: &mut NfStats, t: &render::SynthTally) {
    s.synth_lookups += t.lookups;
    s.synth_hits += t.hits;
    s.synth_proved += t.proved;
    s.synth_refuted += t.refuted;
    s.synth_unproved += t.unproved;
}

/// Why a question was declined.
#[derive(Debug)]
enum Decline {
    Unsupported(&'static str),
    Exhausted,
}

/// A node's normal form.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum Form {
    Const(BitVec),
    Bits(Bits),
    Poly(Poly),
}

/// How an atom is rendered.
#[derive(Clone, Debug)]
enum Def {
    /// Input variable.
    Var(u32),
    /// The input subterm as it is.
    Verbatim(u32),
    /// An input subterm (arithmetic read by a bitwise operator), rendered from its normal form.
    Form(u32),
    /// The complement of an input subterm (arithmetic read by a bitwise operator, which reads
    /// the atom complemented), rendered from its normal form.
    Complement(u32),
    /// `a >> k` of an input subterm `a`, rendered from `a`'s normal form.
    Shift(u16, u32),
}

/// What identifies an atom: equal keys are equal functions of the variables.
#[derive(Clone, Debug, PartialEq, Eq, Hash)]
enum AtomKey {
    /// A subterm kept as it is, by its structural representative.
    Node(u32),
    /// A subterm by its (reduced) normal form over lower atoms.
    Form(Poly),
    /// `a >> k` by `k` and `a`'s normal form.
    Shift(u16, Poly),
}

/// The state of one question.
struct Pass<'p> {
    p: &'p MbaExpr,
    w: Width,
    opts: NfOptions,
    classes: Classes,
    work: Steps,
    cst: Vec<Option<BitVec>>,
    /// Per input node: its structural representative (equal subterms share one).
    canon: Vec<u32>,
    forms: Vec<Option<Form>>,
    atoms: Vec<Def>,
    /// Per atom: the normal form it is rendered from (for `Def::Form`, `Def::Complement` and
    /// `Def::Shift`).
    atom_nf: Vec<Option<Poly>>,
    /// Atoms by what identifies them.
    atom_of: HashMap<AtomKey, u32>,
    /// Normal forms of the operands of products: factors worth trying when rendering.
    factors: Vec<Poly>,
    /// Every node's values at the refutation sample (up to 64 bits), computed on first need,
    /// with the variables' values: for reading a subterm's bits (see `bitwise_by_bits`).
    sample: Option<Option<Sample>>,
    /// Bitwise forms looked for at the sample so far.
    discoveries: u32,
    /// Whether a bitwise operation was read as halves (see [`Pass::halves`]).
    halved: bool,
}

/// The most bitwise forms a question looks for at the sample (each is proved before use).
const DISCOVERIES: u32 = 4;

/// Values at the refutation sample: per node (empty for one not evaluated), and per variable.
type Sample = (Vec<Vec<u64>>, Vec<Vec<u64>>);

fn solve(p: &MbaExpr, opts: &NfOptions, budget: &MbaBudget, tally: &mut NfStats) -> MbaAnswer {
    match run(p, opts, budget, tally) {
        Ok(a) => a,
        Err(Decline::Exhausted) => MbaAnswer::Exhausted,
        Err(Decline::Unsupported(why)) => MbaAnswer::Unsupported(why.into()),
    }
}

impl Pass<'_> {
    fn charge(&mut self, units: u64) -> Result<(), Decline> {
        use certify::Meter;
        self.work.charge(units).map_err(|()| Decline::Exhausted)
    }

    /// The atom with this key (created on first use).
    fn atom(
        &mut self,
        key: AtomKey,
        def: Def,
        nf: Option<Poly>,
        tally: &mut NfStats,
    ) -> Result<u32, Decline> {
        if let Some(&a) = self.atom_of.get(&key) {
            return Ok(a);
        }
        if self.atoms.len() >= self.opts.max_atoms.min(64) as usize {
            tally.declined_atoms += 1;
            return Err(Decline::Unsupported("too many atoms"));
        }
        self.atoms.push(def);
        self.atom_nf.push(nf);
        tally.atoms += 1;
        let a = self.atoms.len() as u32 - 1;
        self.atom_of.insert(key, a);
        Ok(a)
    }

    /// Input node `i` as an atom kept as it is.
    fn verbatim_atom(&mut self, i: u32, tally: &mut NfStats) -> Result<u32, Decline> {
        let key = AtomKey::Node(self.canon[i as usize]);
        self.atom(key, Def::Verbatim(i), None, tally)
    }

    /// A normal form reduced for use as an atom's key (equal functions of lower atoms tend
    /// to get equal keys; unequal ones never do, the reductions being exact).
    fn key_form(&self, p: &Poly) -> Poly {
        key_form(p, &self.classes)
    }

    /// A degree-≤1 form as a bitwise function once atoms stand for multiples of their
    /// definitions (greedily, over the atoms defined by normal forms, while it is not one).
    fn bitwise_over_atoms(&mut self, key: &Poly) -> Result<Option<Bits>, Decline> {
        let mut cur: Option<Poly> = None;
        // Again while something is substituted: one substitution can expose another's
        // definition (`d − (n & s)` with `s = a + d` is `s − a − (n & s)`, then `n = −a`).
        for _ in 0..3 {
            let mut progress = false;
            for a in 0..self.atoms.len() {
                if !matches!(self.atoms[a], Def::Form(_) | Def::Complement(_)) {
                    continue;
                }
                let Some(d) = self.atom_nf[a].clone() else {
                    continue;
                };
                if d.degree() > 1 {
                    continue;
                }
                let base = cur.as_ref().unwrap_or(key);
                self.charge((d.len() + base.len()) as u64 * 4)?;
                // The atom for a multiple of its definition, or, when only a variable of the
                // definition is there, that variable eliminated (`d` is `s − a` for the atom
                // `s = a + d`).
                let whole = if self.classes.len() <= 1 { 0 } else { FULL };
                let Some(sub) = base.substitute(a as u32, &d).or_else(|| {
                    eliminate_var(base, a as u32, &d, self.p.vars().len() as u32, whole)
                }) else {
                    continue;
                };
                self.charge((sub.len() as u64) << sub.atoms().count_ones().min(12))?;
                // The atom stands unmasked: in every class.
                let sub = sub.expand_full(&self.classes);
                if let Some(f) = Bits::from_linear(&sub, &self.classes) {
                    return Ok(Some(f));
                }
                cur = Some(sub);
                progress = true;
            }
            if !progress {
                break;
            }
        }
        Ok(None)
    }

    /// The question's node values and variable values at the refutation sample (points in
    /// lanes of 64 bits: `None` for wider questions).
    fn sample(&mut self) -> Result<Option<&Sample>, Decline> {
        if self.sample.is_none() {
            let computed = (|| {
                let prog = crate::mba::batch::Program::new(self.p, true)?;
                if prog.widest() > 64 {
                    return None;
                }
                let points = certify::sample_points(self.p.vars(), &[self.p], self.p.key()[0]);
                let inputs: Vec<Vec<u64>> = (0..self.p.vars().len())
                    .map(|v| {
                        points
                            .iter()
                            .map(|pt| pt[v].limbs().first().copied().unwrap_or(0))
                            .collect()
                    })
                    .collect();
                let mut regs: Vec<Vec<u64>> = Vec::new();
                prog.run(&mut regs, &inputs, points.len());
                let values = (0..self.p.nodes().len())
                    .map(|i| prog.reg_of(i).map_or_else(Vec::new, |r| regs[r].clone()))
                    .collect();
                Some((values, inputs))
            })();
            let units = (self.p.nodes().len() * certify::SAMPLE_POINTS) as u64;
            self.charge(units.div_ceil(EVALS_PER_STEP))?;
            self.sample = Some(computed);
        }
        Ok(self.sample.as_ref().and_then(Option::as_ref))
    }

    /// Atom `a`'s values at the sample.
    fn atom_values(&mut self, a: u32) -> Result<Option<Vec<u64>>, Decline> {
        let def = self.atoms[a as usize].clone();
        let bits = self.w.bits();
        let mask = if bits >= 64 {
            u64::MAX
        } else {
            (1u64 << bits) - 1
        };
        let Some((values, inputs)) = self.sample()? else {
            return Ok(None);
        };
        let col = |i: u32| values.get(i as usize).filter(|v| !v.is_empty()).cloned();
        Ok(match def {
            Def::Var(v) => inputs.get(v as usize).cloned(),
            Def::Verbatim(i) | Def::Form(i) => col(i),
            Def::Complement(i) => col(i).map(|v| v.iter().map(|x| !x & mask).collect()),
            Def::Shift(k, i) => col(i).map(|v| v.iter().map(|x| x >> k).collect()),
        })
    }

    /// Arithmetic `i` (normal form `key`) read by a bitwise operator, when it is a bitwise
    /// function of the atoms it mentions in a way no linear reading shows (`−(x & −x)` is
    /// `x | −x`): the function its bits follow at the sample, per class, used once a
    /// certificate proves the subterm equal to it.
    fn bitwise_by_bits(
        &mut self,
        i: u32,
        key: &Poly,
        tally: &mut NfStats,
    ) -> Result<Option<Bits>, Decline> {
        let atoms = key.atoms();
        let mut leaves: Vec<u32> = (0..64).filter(|&a| atoms >> a & 1 == 1).collect();
        if self.discoveries >= DISCOVERIES || leaves.is_empty() || leaves.len() > 4 {
            return Ok(None);
        }
        // Over the variables alone a form of degree at most 1 is canonical: it is a bitwise
        // function exactly when `Bits::from_linear` reads it as one (which the caller tried).
        let vars = self.p.vars().len() as u32;
        if key.degree() <= 1 && leaves.iter().all(|&a| a < vars) {
            return Ok(None);
        }
        // And the variables, while there is room: a subterm can be a bitwise function of an
        // atom and the variables inside it together (`−(a & x)` with `a = −(x & y)` is
        // `(a & ~x) | (x & y)`).
        for v in 0..self.p.vars().len() as u32 {
            if leaves.len() < 4
                && !leaves.contains(&v)
                && matches!(self.atoms.get(v as usize), Some(Def::Var(_)))
            {
                leaves.push(v);
            }
        }
        leaves.sort_unstable();
        let Some((values, _)) = self.sample()? else {
            return Ok(None);
        };
        let Some(own) = values.get(i as usize).filter(|v| !v.is_empty()).cloned() else {
            return Ok(None);
        };
        let mut cols = Vec::with_capacity(leaves.len());
        for &a in &leaves {
            match self.atom_values(a)? {
                Some(v) => cols.push(v),
                None => return Ok(None),
            }
        }
        let n = self.classes.len();
        let bits = self.w.bits();
        let class_of: Vec<usize> = (0..bits)
            .map(|j| {
                (0..n)
                    .find(|&c| self.classes.mask(c).bit(j) == Some(true))
                    .unwrap_or(0)
            })
            .collect();
        self.charge((own.len() * usize::from(bits) * leaves.len()) as u64 / EVALS_PER_STEP + 1)?;
        let (mut seen, mut ones) = (vec![0u64; n], vec![0u64; n]);
        for (p, &v) in own.iter().enumerate() {
            for j in 0..bits {
                let e = cols
                    .iter()
                    .enumerate()
                    .fold(0u32, |e, (t, col)| e | (((col[p] >> j) & 1) as u32) << t);
                let (c, bit) = (class_of[usize::from(j)], (v >> j) & 1);
                if seen[c] >> e & 1 == 1 {
                    if ones[c] >> e & 1 != bit {
                        return Ok(None);
                    }
                } else {
                    seen[c] |= 1 << e;
                    ones[c] |= bit << e;
                }
            }
        }
        // A form the sample agrees with: only these count as discoveries (each costs a proof).
        self.discoveries += 1;
        let f = Bits {
            support: leaves.clone(),
            tables: ones.iter().map(|&t| vec![t]).collect(),
        };
        // The proof: the subterm against the function of the atoms' own expressions, class by
        // class under its mask.
        let internal = || Decline::Unsupported("internal: bitwise form");
        let lhs = verbatim(self.p, i).ok_or_else(internal)?;
        let mut b = Builder::new(self.p.vars().to_vec());
        let mut ins = Vec::with_capacity(leaves.len());
        for &a in &leaves {
            let x = match self.atoms[a as usize] {
                Def::Var(v) => b.var(v),
                Def::Verbatim(k) | Def::Form(k) => b
                    .import(&verbatim(self.p, k).ok_or_else(internal)?)
                    .ok_or_else(internal)?,
                Def::Complement(k) => {
                    let x = b
                        .import(&verbatim(self.p, k).ok_or_else(internal)?)
                        .ok_or_else(internal)?;
                    b.un(MOp::Not, x)
                }
                Def::Shift(k, j) => {
                    let x = b
                        .import(&verbatim(self.p, j).ok_or_else(internal)?)
                        .ok_or_else(internal)?;
                    b.un(MOp::LShr(k), x)
                }
            };
            ins.push(x);
        }
        let mut acc: Option<u32> = None;
        for (c, &t) in ones.iter().enumerate() {
            // The algebraic normal form of this class's table.
            let k = leaves.len();
            let mut anf: Vec<bool> = (0..1usize << k).map(|e| t >> e & 1 == 1).collect();
            for bit in 0..k {
                for e in 0..1usize << k {
                    if e >> bit & 1 == 1 {
                        anf[e] ^= anf[e ^ 1 << bit];
                    }
                }
            }
            let mut g: Option<u32> = None;
            for (e, &on) in anf.iter().enumerate().skip(1) {
                if !on {
                    continue;
                }
                let mut m: Option<u32> = None;
                for (t, &x) in ins.iter().enumerate() {
                    if e >> t & 1 == 1 {
                        m = Some(match m {
                            None => x,
                            Some(y) => b.bin(MOp::And, y, x),
                        });
                    }
                }
                if let Some(m) = m {
                    g = Some(match g {
                        None => m,
                        Some(y) => b.bin(MOp::Xor, y, m),
                    });
                }
            }
            let mut g = g.unwrap_or_else(|| b.konst(&BitVec::zero(self.w)));
            if anf[0] {
                g = b.un(MOp::Not, g);
            }
            if n > 1 {
                let m = b.konst(self.classes.mask(c));
                g = b.bin(MOp::And, g, m);
            }
            acc = Some(match acc {
                None => g,
                Some(y) => b.bin(MOp::Or, y, g),
            });
        }
        let rhs = b.finish(acc.ok_or_else(internal)?).ok_or_else(internal)?;
        let report = certify_within(&lhs, &rhs, &mut self.work);
        tally.certificates.record(&report);
        Ok((report.verdict == Verdict::Proved).then(|| f.prune()))
    }

    /// Node `i` read by a bitwise operator: its bitwise function (an atom when it is not one).
    fn bitwise(&mut self, i: u32, tally: &mut NfStats) -> Result<Bits, Decline> {
        let n = self.classes.len();
        match self.forms[i as usize].clone() {
            Some(Form::Const(v)) => {
                let bits: Option<Vec<bool>> = (0..n).map(|c| self.classes.bit(&v, c)).collect();
                bits.map(|b| Bits::constant(&b))
                    .ok_or(Decline::Unsupported("a constant splits a bit class"))
            }
            Some(Form::Bits(f)) => Ok(f),
            Some(Form::Poly(p)) => {
                // Arithmetic that is secretly a bitwise function is read as one, also once
                // other atoms stand for their definitions (`(~a & d) − e` with `a` the atom
                // `−e` is `d | a`); otherwise it is an atom, identified by its normal form.
                let key = self.key_form(&p);
                if key.degree() <= 1 {
                    self.charge((key.len() as u64) << key.atoms().count_ones().min(12))?;
                    if let Some(f) = Bits::from_linear(&key, &self.classes) {
                        return Ok(f);
                    }
                    if let Some(f) = self.bitwise_over_atoms(&key)? {
                        return Ok(f);
                    }
                }
                if let Some(f) = self.bitwise_by_bits(i, &key, tally)? {
                    return Ok(f);
                }
                // Atoms are one up to complement: of `p` and `~p = −1 − p`, the one with the
                // smaller constant (`−x` for `x − 1`), so a bitwise reader of either reads the
                // same atom, complemented or not.
                let not = self.key_form(&Poly::constant(BitVec::ones(self.w)).sub(&p));
                let complement =
                    BitVec::cmp_unchecked(crate::ops::CmpOp::Ult, &not.konst(), &key.konst());
                let (key, def) = if complement {
                    (not, Def::Complement(i))
                } else {
                    (key, Def::Form(i))
                };
                let a = self.atom(AtomKey::Form(key.clone()), def, Some(key), tally)?;
                let f = Bits::atom(n, a);
                Ok(if complement { f.not() } else { f })
            }
            None => {
                let a = self.verbatim_atom(i, tally)?;
                Ok(Bits::atom(n, a))
            }
        }
    }

    /// Node `i` read arithmetically: its polynomial.
    fn poly(&mut self, i: u32, tally: &mut NfStats) -> Result<Poly, Decline> {
        let f = match self.forms[i as usize].clone() {
            Some(f) => f,
            None => {
                let a = self.verbatim_atom(i, tally)?;
                Form::Bits(Bits::atom(self.classes.len(), a))
            }
        };
        let p = match f {
            Form::Const(v) => Poly::constant(v),
            Form::Bits(b) => {
                self.charge((b.tables.len() as u64) << b.support.len())?;
                let p = b.to_poly(&self.classes);
                if p.len() > self.opts.max_terms as usize {
                    // Too many monomials to take part in arithmetic: an atom.
                    tally.declined_terms += 1;
                    let a = self.verbatim_atom(i, tally)?;
                    Bits::atom(self.classes.len(), a).to_poly(&self.classes)
                } else {
                    p
                }
            }
            Form::Poly(p) => p,
        };
        Ok(p)
    }

    /// Remembers the normal form of a product's operand: rendering tries it as a factor. A
    /// single monomial is not one: rendering takes out common symbols anyway.
    fn note_factor(&mut self, f: &Poly) {
        if f.degree() >= 1
            && (2..=64).contains(&f.len())
            && self.factors.len() < 16
            && !self.factors.contains(f)
        {
            self.factors.push(f.clone());
        }
    }

    /// Node `i` as an atom (a sum or product too large to keep multiplied out).
    fn opaque(&mut self, i: u32, tally: &mut NfStats) -> Result<Option<Form>, Decline> {
        tally.declined_terms += 1;
        let at = self.verbatim_atom(i, tally)?;
        Ok(Some(Form::Bits(Bits::atom(self.classes.len(), at))))
    }

    /// `a op b` (`op` bitwise) as arithmetic when one operand is a constant that reads only
    /// known low bits of the other's polynomial (see [`known_bits`]).
    fn known_bits(&mut self, op: MOp, a: u32, b: u32) -> Result<Option<Form>, Decline> {
        let (x, k) = match (self.cst[a as usize], self.cst[b as usize]) {
            (None, Some(k)) => (a, k),
            (Some(k), None) => (b, k),
            _ => return Ok(None),
        };
        let Some(Form::Poly(p)) = &self.forms[x as usize] else {
            return Ok(None);
        };
        let p = p.clone();
        self.charge(p.len() as u64)?;
        Ok(known_bits(op, &p, &self.classes, &k).map(Form::Poly))
    }

    /// `a op b` (`op` bitwise) for operands that are both multiples of `2^k` as polynomials
    /// (every coefficient and the constant): bitwise operators commute with a left shift, so
    /// it is `2^k·(a/2^k op b/2^k)`, arithmetic, when the halves are bitwise functions
    /// (`(y + y) ^ ((x ^ z) + x − z)` is `2·(y ^ (x & ~z))`).
    fn halves(&mut self, op: MOp, a: u32, b: u32) -> Result<Option<Form>, Decline> {
        let w = self.w;
        let operand = |s: &Self, i: u32| -> Option<Poly> {
            match &s.forms[i as usize] {
                Some(Form::Poly(p)) => Some(p.clone()),
                Some(Form::Const(v)) => Some(Poly::constant(*v)),
                _ => None,
            }
        };
        let (Some(pa), Some(pb)) = (operand(self, a), operand(self, b)) else {
            return Ok(None);
        };
        // Both constants fold elsewhere.
        if pa.len() <= 1 && pb.len() <= 1 && pa.degree() == 0 && pb.degree() == 0 {
            return Ok(None);
        }
        self.charge((pa.len() + pb.len()) as u64)?;
        let tz = |p: &Poly| {
            p.terms()
                .values()
                .map(crate::facts::known::trailing_zeros)
                .min()
                .unwrap_or(u32::from(w.bits()))
        };
        let k = tz(&pa).min(tz(&pb)).min(u32::from(w.bits()) - 1);
        if k == 0 {
            return Ok(None);
        }
        let amount = BitVec::wrapping_from_u64(w, u64::from(k));
        let half = |p: &Poly| {
            let mut q = Poly::zero(w);
            for (m, c) in p.terms() {
                q.add_term(
                    m.clone(),
                    &BitVec::bin_unchecked(crate::ops::BinOp::AShr, c, &amount),
                );
            }
            q
        };
        let (ha, hb) = (half(&pa), half(&pb));
        let (Some(x), Some(y)) = (
            Bits::from_linear(&ha.expand_full(&self.classes), &self.classes),
            Bits::from_linear(&hb.expand_full(&self.classes), &self.classes),
        ) else {
            return Ok(None);
        };
        let bop = match op {
            MOp::And => BitOp::And,
            MOp::Or => BitOp::Or,
            _ => BitOp::Xor,
        };
        let Some(r) = Bits::bin(bop, &x, &y) else {
            return Ok(None);
        };
        let scale = crate::facts::known::bv_shl(&BitVec::one(w), k);
        Ok(Some(Form::Poly(r.to_poly(&self.classes).scale(&scale))))
    }

    /// The normal form of live node `i` from its operands' forms.
    fn visit(&mut self, i: u32, tally: &mut NfStats) -> Result<Option<Form>, Decline> {
        let n = self.p.nodes()[i as usize];
        if let Some(v) = self.cst[i as usize] {
            return Ok(Some(Form::Const(v)));
        }
        if n.width != self.w {
            // Below a cast: rendered as it is, inside the cast's atom.
            return Ok(None);
        }
        let (a, b) = (n.args[0], n.args[1]);
        let w = self.w;
        Ok(Some(match n.op {
            MOp::Var(v) => {
                if self.p.vars()[v as usize] != w {
                    return Err(Decline::Unsupported("a variable of another width"));
                }
                Form::Bits(Bits::atom(self.classes.len(), v))
            }
            MOp::And | MOp::Or | MOp::Xor => {
                if let Some(f) = self.known_bits(n.op, a, b)? {
                    tally.known_bits += 1;
                    return Ok(Some(f));
                }
                if let Some(f) = self.halves(n.op, a, b)? {
                    tally.known_bits += 1;
                    self.halved = true;
                    return Ok(Some(f));
                }
                let (x, y) = (self.bitwise(a, tally)?, self.bitwise(b, tally)?);
                self.charge((x.tables.len() as u64) << (x.support.len() + y.support.len()))?;
                let op = match n.op {
                    MOp::And => BitOp::And,
                    MOp::Or => BitOp::Or,
                    _ => BitOp::Xor,
                };
                match Bits::bin(op, &x, &y) {
                    Some(f) => Form::Bits(f),
                    None => {
                        // A bitwise function of too many atoms: an atom itself.
                        let at = self.verbatim_atom(i, tally)?;
                        Form::Bits(Bits::atom(self.classes.len(), at))
                    }
                }
            }
            MOp::Not => match self.forms[a as usize].clone() {
                Some(Form::Bits(f)) => Form::Bits(f.not()),
                _ => {
                    let x = self.poly(a, tally)?;
                    Form::Poly(Poly::constant(BitVec::ones(w)).sub(&x))
                }
            },
            MOp::Add | MOp::Sub => {
                let (x, y) = (self.poly(a, tally)?, self.poly(b, tally)?);
                self.charge((x.len() + y.len()) as u64)?;
                let r = if n.op == MOp::Add {
                    x.add(&y)
                } else {
                    x.sub(&y)
                };
                if r.len() > self.opts.max_terms as usize {
                    return self.opaque(i, tally);
                }
                Form::Poly(r)
            }
            MOp::Neg => Form::Poly(self.poly(a, tally)?.neg()),
            MOp::Shl(k) => {
                let x = self.poly(a, tally)?;
                let s = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(k));
                Form::Poly(x.scale(&s))
            }
            MOp::Mul => match (self.cst[a as usize], self.cst[b as usize]) {
                (Some(k), _) => Form::Poly(self.poly(b, tally)?.scale(&k)),
                (_, Some(k)) => Form::Poly(self.poly(a, tally)?.scale(&k)),
                _ => {
                    let (mut x, mut y) = (self.poly(a, tally)?, self.poly(b, tally)?);
                    let cap = self.opts.max_degree;
                    // Over the degree cap, the exact reductions first: high powers fold into
                    // lower degrees (at 8 bits every power from x^10 on), so a product is an
                    // atom only when its degree stays over the cap.
                    if x.degree() + y.degree() > cap {
                        self.charge(((x.len() + y.len()) as u64) * u64::from(cap))?;
                        x.reduce_core(&self.classes);
                        y.reduce_core(&self.classes);
                    }
                    let size = (x.len() as u64).saturating_mul(y.len() as u64);
                    let max = u64::from(self.opts.max_terms);
                    if size > max.saturating_mul(4) || x.degree() + y.degree() > cap {
                        return self.opaque(i, tally);
                    }
                    self.charge(size)?;
                    self.note_factor(&x);
                    self.note_factor(&y);
                    let prod = x.mul(&y);
                    if prod.len() as u64 > max {
                        return self.opaque(i, tally);
                    }
                    Form::Poly(prod)
                }
            },
            MOp::LShr(k) => {
                // A right shift: an atom, identified by the amount and its operand's form.
                let x = self.poly(a, tally)?;
                let key = self.key_form(&x);
                let at = self.atom(
                    AtomKey::Shift(k, key.clone()),
                    Def::Shift(k, a),
                    Some(key),
                    tally,
                )?;
                Form::Bits(Bits::atom(self.classes.len(), at))
            }
            MOp::Zext | MOp::Sext | MOp::Trunc | MOp::Const(_) => {
                let at = self.verbatim_atom(i, tally)?;
                Form::Bits(Bits::atom(self.classes.len(), at))
            }
        }))
    }
}

/// The constants read by bitwise operators among the live nodes of width `w`: they define the
/// bit classes.
fn class_constants(p: &MbaExpr, live: &[bool], cst: &[Option<BitVec>], w: Width) -> Vec<BitVec> {
    let mut consts: Vec<BitVec> = Vec::new();
    for (i, n) in p.nodes().iter().enumerate() {
        if live[i]
            && n.width == w
            && cst[i].is_none()
            && matches!(n.op, MOp::And | MOp::Or | MOp::Xor)
        {
            for &k in &n.args[..2] {
                if let Some(v) = cst[k as usize] {
                    consts.push(v);
                }
            }
        }
    }
    consts
}

/// See [`Pass::key_form`].
fn key_form(p: &Poly, classes: &Classes) -> Poly {
    let mut k = p.clone();
    k.reduce_core(classes);
    k.single_positions(classes);
    k.reduce_core(classes);
    k
}

/// `p op k` (`op` bitwise, `k` a constant) as a polynomial, when `k` reads only low bits of
/// `p` that are known (every non-constant monomial is a multiple of `2^j`, so the low `j` bits
/// are the constant term's) and is all zeros or all ones above them. Setting, clearing or
/// flipping known bits adds a constant; above them the result is `p`, `~p`, zeros or ones. For
/// example `−2·(x & 1) | 1` is `1 − 2·(x & 1)`.
fn known_bits(op: MOp, p: &Poly, classes: &Classes, k: &BitVec) -> Option<Poly> {
    use crate::facts::known::{bv_and, bv_not, bv_or};
    let w = p.width();
    let j = p.known_low_bits(classes);
    if j == 0 {
        return None;
    }
    let low = crate::facts::known::low_mask(w, j);
    // The known bits, and `k` inside and above them.
    let r = bv_and(&p.konst(), &low);
    let kl = bv_and(k, &low);
    let above = bv_and(k, &bv_not(&low));
    // `q + add − sub`.
    let shift =
        |q: &Poly, add: BitVec, sub: BitVec| q.add(&Poly::constant(add)).sub(&Poly::constant(sub));
    let zero = BitVec::zero(w);
    if above.is_zero() {
        Some(match op {
            MOp::And => Poly::constant(bv_and(&r, &kl)),
            MOp::Or => shift(p, bv_and(&kl, &bv_not(&r)), zero),
            _ => shift(p, bv_and(&kl, &bv_not(&r)), bv_and(&kl, &r)),
        })
    } else if above == bv_not(&low) {
        Some(match op {
            MOp::And => shift(p, zero, bv_and(&r, &bv_not(&kl))),
            MOp::Or => Poly::constant(bv_or(k, &r)),
            _ => {
                // `p ^ k = ~p ^ (low & ~k)`, and the known bits of `~p` are `~r`.
                let not_p = Poly::constant(BitVec::ones(w)).sub(p);
                let c = bv_and(&low, &bv_not(&kl));
                shift(&not_p, bv_and(&c, &r), bv_and(&c, &bv_not(&r)))
            }
        })
    } else {
        None
    }
}

/// The nodes the root uses.
fn live(p: &MbaExpr) -> Vec<bool> {
    let nodes = p.nodes();
    let mut live = vec![false; nodes.len()];
    if let Some(r) = live.last_mut() {
        *r = true;
    }
    for i in (0..nodes.len()).rev() {
        if live[i] {
            let n = &nodes[i];
            for &k in &n.args[..n.op.arity()] {
                live[k as usize] = true;
            }
        }
    }
    live
}

/// Per node: a representative among structurally equal nodes (commutative operands in either
/// order), and the number of distinct live nodes.
fn canonical(p: &MbaExpr, live: &[bool]) -> (Vec<u32>, u32) {
    let mut intern: HashMap<MNode, u32> = HashMap::new();
    let mut canon = Vec::with_capacity(p.nodes().len());
    let mut distinct = 0;
    for (i, n) in p.nodes().iter().enumerate() {
        let mut key = *n;
        for k in 0..n.op.arity() {
            key.args[k] = canon[n.args[k] as usize];
        }
        if matches!(key.op, MOp::Add | MOp::Mul | MOp::And | MOp::Or | MOp::Xor)
            && key.args[0] > key.args[1]
        {
            key.args.swap(0, 1);
        }
        let c = *intern.entry(key).or_insert_with(|| {
            if live[i] {
                distinct += 1;
            }
            i as u32
        });
        canon.push(c);
    }
    // A shift's amount is a constant node once lifted (shared with an equal constant): count
    // it as the candidates' costs do.
    let mut consts: Vec<BitVec> = p
        .nodes()
        .iter()
        .zip(live)
        .filter_map(|(n, &l)| match n.op {
            MOp::Const(v) if l => Some(v),
            _ => None,
        })
        .collect();
    for (n, &l) in p.nodes().iter().zip(live) {
        if let MOp::Shl(k) | MOp::LShr(k) = n.op
            && l
        {
            let v = BitVec::wrapping_from_u64(n.width, u64::from(k));
            if !consts.contains(&v) {
                consts.push(v);
                distinct += 1;
            }
        }
    }
    (canon, distinct)
}

/// The input subterm at `i`, copied as it is.
fn verbatim(p: &MbaExpr, i: u32) -> Option<MbaExpr> {
    let mut b = Builder::new(p.vars().to_vec());
    let mut map: HashMap<u32, u32> = HashMap::new();
    let nodes = p.nodes();
    // The nodes below i, operands first.
    let mut need = vec![false; i as usize + 1];
    need[i as usize] = true;
    for j in (0..=i as usize).rev() {
        if need[j] {
            let n = &nodes[j];
            for &k in &n.args[..n.op.arity()] {
                need[k as usize] = true;
            }
        }
    }
    for j in 0..=i as usize {
        if !need[j] {
            continue;
        }
        let n = &nodes[j];
        let arg = |k: usize| map[&n.args[k]];
        let id = match n.op {
            MOp::Const(v) => b.konst(&v),
            MOp::Var(v) => b.var(v),
            MOp::Zext | MOp::Sext | MOp::Trunc => b.cast(n.op, arg(0), n.width),
            op if op.arity() == 1 => b.un(op, arg(0)),
            op => b.bin(op, arg(0), arg(1)),
        };
        map.insert(j as u32, id);
    }
    b.finish(map[&i])
}

/// A question's normal form, ready to render.
struct Normal {
    w: Width,
    /// The question's variables (the first atoms).
    vars: u32,
    classes: Classes,
    nf: Poly,
    /// The same function with atoms standing for their definitions where these appear
    /// arithmetically (rendered too; the cheapest wins).
    alts: Vec<Poly>,
    /// The atoms and their normal forms (see [`more_forms`]).
    defs: Vec<Def>,
    atom_nf: Vec<Option<Poly>>,
    atom_exprs: Vec<MbaExpr>,
    factors: Vec<Poly>,
    /// Masked conjunctions proved zero (see [`prune_null_conjunctions`]).
    nulls: Vec<poly::Sym>,
    /// Whether a bitwise operation was read as halves.
    halved: bool,
    input_cost: u32,
    work: Steps,
    synthesis: bool,
    max_terms: u32,
}

/// A normal form as rendered: unmasked symbols wherever the classes allow (the same function;
/// `nulls` are masked conjunctions known to be zero), then the one-position rule.
fn finished(f: &Poly, classes: &Classes, nulls: &[poly::Sym]) -> Poly {
    // With one class an unmasked symbol is that class's (substitution writes unmasked atoms):
    // one symbol either way.
    let mut f = if classes.len() <= 1 {
        f.expand_full(classes)
    } else {
        f.clone()
    };
    f.reduce_core(classes);
    let mut f = f.declass(classes, DECLASS_LIMIT, nulls);
    f.single_positions(classes);
    f.reduce_core(classes);
    f
}

fn normalize(
    input: &MbaExpr,
    opts: &NfOptions,
    budget: &MbaBudget,
    tally: &mut NfStats,
) -> Result<Normal, Decline> {
    let Some(w) = input.width() else {
        return Err(Decline::Unsupported("empty"));
    };
    // Bitwise operations with constants that read only bits the facts know are read as
    // arithmetic first (as the certificates read them) where that leaves fewer bit classes:
    // `x·−100 | 1` is `x·−100 + 1`, a polynomial in `x`. (With as many classes, the question
    // stays as asked: its own spelling is often the better start.)
    let classes_of = |m: &MbaExpr| {
        let live = live(m);
        let consts = class_constants(m, &live, &certify::constants(m.nodes()), w);
        Classes::new(w, &consts, opts.max_classes as usize).map_or(usize::MAX, |c| c.len())
    };
    let lowered = certify::lower_known_bits(input).filter(|l| classes_of(l) < classes_of(input));
    tally.lowered += u64::from(lowered.is_some());
    let p = lowered.as_ref().unwrap_or(input);
    let nodes = p.nodes();
    let live = live(p);
    let cst = certify::constants(nodes);
    // Operators other than casts have operands of their own width, so nodes of another width
    // are only below casts, whose atoms render them as they are.
    if p.vars().len() > opts.max_atoms.min(64) as usize {
        tally.declined_atoms += 1;
        return Err(Decline::Unsupported("too many variables"));
    }
    let mut work = Steps::new(budget.steps);
    {
        use certify::Meter;
        // A node visit each, and the facts of the reading above (a transfer of facts costs
        // about as much as evaluating a node at `LOWER_COST` points).
        let facts = if certify::lowerable(input) {
            input.nodes().len() as u64 * certify::LOWER_COST / EVALS_PER_STEP
        } else {
            0
        };
        work.charge(nodes.len() as u64 + facts)
            .map_err(|()| Decline::Exhausted)?;
    }
    let consts = class_constants(p, &live, &cst, w);
    let Some(classes) = Classes::new(w, &consts, opts.max_classes as usize) else {
        tally.declined_classes += 1;
        return Err(Decline::Unsupported("too many bit classes"));
    };
    let (canon, cost) = canonical(p, &live);
    // Answers are measured against the question as asked.
    let input_cost = match lowered {
        Some(_) => canonical(input, &self::live(input)).1,
        None => cost,
    };
    let mut pass = Pass {
        p,
        w,
        opts: *opts,
        classes,
        work,
        cst,
        canon,
        forms: vec![None; nodes.len()],
        atoms: (0..p.vars().len() as u32).map(Def::Var).collect(),
        atom_nf: vec![None; p.vars().len()],
        atom_of: HashMap::new(),
        factors: Vec::new(),
        sample: None,
        discoveries: 0,
        halved: false,
    };
    for (i, &is_live) in live.iter().enumerate() {
        if !is_live {
            continue;
        }
        pass.charge(1)?;
        let f = pass.visit(i as u32, tally)?;
        pass.forms[i] = f;
    }
    let root = nodes.len() as u32 - 1;
    let mut nf = pass.poly(root, tally)?;
    pass.charge(nf.len() as u64 * u64::from(nf.degree() + 1))?;
    // The exact reductions; the one-position rule comes after unmasking (below), which it
    // would otherwise hide from.
    nf.reduce_core(&pass.classes);
    // Telemetry: the fragment reached.
    if pass.atoms.len() > p.vars().len() {
        tally.abstracted += 1;
    }
    if nf.degree() > 1 {
        tally.polynomial += 1;
    } else if pass.classes.len() > 1 {
        tally.semilinear += 1;
    } else {
        tally.linear += 1;
    }
    let finish = |f: &Poly| finished(f, &pass.classes, &[]);
    let mut factors: Vec<Poly> = pass.factors.iter().map(finish).collect();
    let mut work = pass.work;
    // The atoms' renderings, lower atoms first: each once, from its own cheapest form (the
    // subterm as it is among the candidates).
    let mut atom_exprs: Vec<MbaExpr> = Vec::with_capacity(pass.atoms.len());
    for (a, def) in pass.atoms.iter().enumerate() {
        let internal = || Decline::Unsupported("internal: atom rendering");
        let e = match *def {
            Def::Var(v) => {
                let mut m = MbaExpr::new(p.vars().to_vec());
                m.push(MOp::Var(v), &[]).map_err(|_| internal())?;
                m
            }
            Def::Verbatim(i) => verbatim(p, i).ok_or_else(internal)?,
            Def::Form(i) | Def::Complement(i) | Def::Shift(_, i) => {
                let form = finish(pass.atom_nf[a].as_ref().ok_or_else(internal)?);
                // Without the searches meant for a question's own form.
                let mut r = Render::new(
                    p.vars().to_vec(),
                    w,
                    &pass.classes,
                    &atom_exprs[..a],
                    work.left,
                )
                .for_atom();
                // The subterm as it is: a rendering of the form replaces it only with fewer
                // nodes.
                let as_is = verbatim(p, i)
                    .and_then(|v| r.b.import(&v))
                    .map(|root| match *def {
                        Def::Complement(_) => r.b.un(MOp::Not, root),
                        _ => root,
                    });
                if let Some(x) = as_is {
                    let bar = r.b.cost(x).0;
                    r = r.with_bar(bar);
                }
                let mut cands = candidates(&mut r, &form, &factors);
                cands.extend(as_is);
                if opts.synthesis && !r.hopeless(form.atoms()) {
                    let bar = r.best(&cands).map(|b| r.b.cost(b));
                    if let Some(render::Hit::Exact(x)) = r.synthesize(&form, bar) {
                        cands.push(x);
                    }
                    add_synth(tally, &r.synth);
                }
                {
                    use certify::Meter;
                    work.charge(r.work.max(1))
                        .map_err(|()| Decline::Exhausted)?;
                }
                tally.candidates += r.built;
                let best = r.best(&cands).ok_or_else(internal)?;
                let body = r.b.finish(best).ok_or_else(internal)?;
                match *def {
                    Def::Shift(k, _) => {
                        let mut b = Builder::new(p.vars().to_vec());
                        let x = b.import(&body).ok_or_else(internal)?;
                        let y = b.un(MOp::LShr(k), x);
                        b.finish(y).ok_or_else(internal)?
                    }
                    _ => body,
                }
            }
        };
        atom_exprs.push(e);
    }
    let mut nulls = Vec::new();
    prune_null_conjunctions(
        p,
        &mut nf,
        &pass.classes,
        &atom_exprs,
        &mut nulls,
        &mut work,
        tally,
    )?;
    // For the question's own rendering (not its atoms'), sums and differences of two factors,
    // where no longer than either: `x·y` written `(x & y)·(x | y) + (x & ~y)·(~x & y)` has the
    // factors `x = (x & y) + (x & ~y)` and `y = (x | y) − (x & ~y)`.
    let noted = factors.len().min(FACTORS_PAIRED);
    for i in 0..noted {
        for j in i + 1..noted {
            let most = factors[i].len().min(factors[j].len());
            for f in [factors[i].add(&factors[j]), factors[i].sub(&factors[j])] {
                if f.degree() >= 1 && (2..=most).contains(&f.len()) && !factors.contains(&f) {
                    factors.push(f);
                }
            }
        }
    }
    drop_dependent_atoms(
        p,
        &mut nf,
        &pass.classes,
        &pass.atoms,
        &atom_exprs,
        &mut work,
        tally,
    )?;
    if nf.degree() >= 2 {
        prune_null(p, &mut nf, &pass.classes, &atom_exprs, &mut work, tally)?;
    }
    {
        use certify::Meter;
        let n = pass.classes.len() as u64;
        work.charge((nf.len() as u64).saturating_mul(n * n))
            .map_err(|()| Decline::Exhausted)?;
    }
    // Atom reuse: where the definition of an atom (arithmetic read by a bitwise operator)
    // also appears arithmetically, a multiple of it becomes the atom, which the rendering then
    // shares with the bitwise uses. Greedy over the atoms, while the finished form does not
    // grow.
    // Known-zero conjunctions are don't-cares when unmasking.
    let finish = |f: &Poly| finished(f, &pass.classes, &nulls);
    let mut alt: Option<Poly> = None;
    let mut alt_len: Option<usize> = None;
    let mut reused = false;
    for (a, def) in pass.atoms.iter().enumerate() {
        let (Def::Form(_) | Def::Complement(_), Some(d)) = (def, pass.atom_nf[a].as_ref()) else {
            continue;
        };
        if nf.len() > REUSE_TERMS {
            break;
        }
        // Below degree 2 the form is its own key form: a quick look first.
        let base = alt.as_ref().unwrap_or(&nf);
        if base.degree() <= 1 && d.pivot().is_none_or(|(m, _)| !base.terms().contains_key(m)) {
            continue;
        }
        let cur = alt.get_or_insert_with(|| key_form(&nf, &pass.classes));
        {
            use certify::Meter;
            work.charge((d.len() + cur.len()) as u64 * 4)
                .map_err(|()| Decline::Exhausted)?;
        }
        if let Some(s) = cur.substitute(a as u32, d) {
            let base = *alt_len.get_or_insert_with(|| finish(cur).len());
            let len = finish(&s).len();
            if len <= base {
                (*cur, alt_len, reused) = (s, Some(len), true);
            }
        }
    }
    let alts = match alt {
        Some(alt) if reused => vec![finish(&alt)],
        _ => Vec::new(),
    };
    let nf = finish(&nf);
    let alts: Vec<Poly> = alts.into_iter().filter(|a| *a != nf).collect();
    tally.reused += u64::from(!alts.is_empty());
    Ok(Normal {
        w,
        vars: p.vars().len() as u32,
        classes: pass.classes,
        nf,
        alts,
        defs: pass.atoms,
        atom_nf: pass.atom_nf,
        atom_exprs,
        factors,
        nulls,
        halved: pass.halved,
        input_cost,
        work,
        synthesis: opts.synthesis,
        max_terms: opts.max_terms,
    })
}

/// Other forms of the normal form's function, rendered beside it (see `best_rendering`): a
/// variable eliminated through an atom's definition, and zero added to complete a bitwise
/// function of an atom.
fn more_forms(n: &Normal, work: &mut Steps) -> Result<Vec<Poly>, Decline> {
    let w = n.w;
    let nf = &n.nf;
    let finish = |f: &Poly| finished(f, &n.classes, &n.nulls);
    let mut alts: Vec<Poly> = n.alts.clone();
    let known = alts.len();
    // Unmasked symbols in finished forms: `FULL`, or the only class.
    let whole = if n.classes.len() <= 1 { 0 } else { FULL };
    // Elimination: an atom whose definition is linear in the variables, `α·v + …` with `α`
    // odd, determines `v = α⁻¹·(n − …)`; the form with `v` read so wherever it is read
    // arithmetically (`−a·c + c·(n & a) + n·(n & a)` with `n` the atom `−c` is `a·n`).
    let vars = n.vars;
    let mut eliminated = 0;
    for (a, def) in n.defs.iter().enumerate() {
        let (Def::Form(_) | Def::Complement(_), Some(d)) = (def, n.atom_nf[a].as_ref()) else {
            continue;
        };
        let d = finish(d);
        if eliminated == 2 {
            continue;
        }
        let plain = |m: &Mono| {
            matches!(m.as_slice(), [(s, 1)] if s.class == whole
                && s.set.count_ones() == 1
                && s.set.trailing_zeros() < vars)
        };
        // A variable the definition reads once, alone, with an odd coefficient (its other
        // terms need not be linear: `e² + d` determines `d`).
        let once = |v: Sym| {
            d.terms()
                .keys()
                .filter(|t| t.iter().any(|&(s, _)| s.set & v.set != 0))
                .count()
                == 1
        };
        let Some((m, alpha)) = d
            .terms()
            .iter()
            .find(|(m, c)| plain(m) && c.bit(0) == Some(true) && once(m[0].0))
        else {
            continue;
        };
        let v = m[0].0;
        if !nf.terms().keys().any(|t| t.iter().any(|&(s, _)| s == v)) {
            continue;
        }
        // v = α⁻¹·(n − (d − α·v)).
        let mut rest = d.clone();
        rest.add_term(
            m.clone(),
            &BitVec::un_unchecked(crate::ops::UnOp::Neg, alpha),
        );
        let mut r = Poly::sym(
            w,
            Sym {
                set: 1 << a,
                class: whole,
            },
        )
        .sub(&rest);
        r = r.scale(&poly::odd_inverse(alpha));
        {
            use certify::Meter;
            work.charge((nf.len() as u64).saturating_mul(u64::from(nf.degree()) + 1) * 4)
                .map_err(|()| Decline::Exhausted)?;
        }
        if let Some(e) = nf.replace(v, &r, n.max_terms as usize) {
            let e = finish(&e);
            if e != *nf && !alts.contains(&e) {
                alts.push(e);
                eliminated += 1;
            }
        }
    }
    // And zero added: `c·(n − d)` for an atom `n` with a linear definition `d` that the form
    // reads bitwise, `c = ±1`, which completes a bitwise function of it (`−(b & n)` with `n` the
    // atom `−b` is `b + n − (b & n)`, `b | n`). Also to the form with atoms reused, which may
    // read the atom arithmetically where the normal form reads its definition (`(p | (a ^ d)) +
    // (a ^ D)` with `D` the atom `2·a` and `p` the atom `a·d`).
    let mut added = 0;
    for (a, def) in n.defs.iter().enumerate() {
        let (Def::Form(_) | Def::Complement(_), Some(d)) = (def, n.atom_nf[a].as_ref()) else {
            continue;
        };
        if added == 4 || nf.len() > 16 {
            break;
        }
        let d = finish(d);
        let read = nf.terms().keys().any(|m| {
            m.iter()
                .any(|&(s, _)| s.set >> a & 1 == 1 && s.set.count_ones() > 1)
        });
        if d.degree() != 1 || !read {
            continue;
        }
        let zero = Poly::sym(
            w,
            Sym {
                set: 1 << a,
                class: whole,
            },
        )
        .sub(&d);
        {
            use certify::Meter;
            work.charge((nf.len() + zero.len()) as u64 * 8)
                .map_err(|()| Decline::Exhausted)?;
        }
        for base in std::iter::once(nf).chain(&n.alts) {
            for c in [BitVec::one(w), BitVec::ones(w)] {
                let e = finish(&base.add(&zero.scale(&c)));
                if e != *nf && !alts.contains(&e) {
                    alts.push(e);
                    added += 1;
                }
            }
        }
    }
    // And zero that makes the form a bitwise function: one or two relations `n − d` (atoms
    // with linear definitions the form reads) times small multiples, kept only when the sum is
    // one (`−(d & e)` with `e` the atom `−d` is `d | e`: `d + e − (d & e)`, one each of
    // `d − (c − e)` and `e − (e − c)`).
    let reads = |a: usize| {
        nf.terms()
            .keys()
            .any(|m| m.iter().any(|&(s, _)| s.set >> a & 1 == 1))
    };
    let relations: Vec<Poly> = n
        .defs
        .iter()
        .enumerate()
        .filter_map(|(a, def)| match (def, n.atom_nf[a].as_ref()) {
            (Def::Form(_) | Def::Complement(_), Some(d)) if a < 64 && reads(a) => {
                let d = finish(d);
                let atom = Poly::sym(
                    w,
                    Sym {
                        set: 1 << a,
                        class: whole,
                    },
                );
                (d.degree() == 1).then(|| atom.sub(&d))
            }
            _ => None,
        })
        .take(BITWISE_RELATIONS)
        .collect();
    let mut bitwise: Vec<Poly> = Vec::new();
    if !relations.is_empty() && nf.len() <= 32 {
        let small: Vec<BitVec> = [1i128, -1, 2, -2]
            .iter()
            .map(|&k| BitVec::wrapping_from_i128(w, k))
            .collect();
        let mut combos: Vec<Poly> = Vec::new();
        for (i, r) in relations.iter().enumerate() {
            for k in &small {
                let one = r.scale(k);
                for r2 in &relations[i + 1..] {
                    for k2 in &small {
                        combos.push(one.add(&r2.scale(k2)));
                    }
                }
                combos.push(one);
            }
        }
        for base in std::iter::once(nf).chain(&n.alts) {
            if base.degree() > 1 {
                continue;
            }
            for z in &combos {
                {
                    use certify::Meter;
                    let corners = 1u64 << (base.atoms() | z.atoms()).count_ones().min(16);
                    work.charge((base.len() + z.len()) as u64 + corners)
                        .map_err(|()| Decline::Exhausted)?;
                }
                let g = base.add(z);
                // A bitwise function's single atoms have coefficients −1, 0 or 1 (an unmasked
                // one alone, then in every class): most sums fail that first.
                let masked: u64 = g
                    .terms()
                    .keys()
                    .flat_map(|m| m.iter())
                    .filter(|(s, _)| s.class != whole)
                    .fold(0, |a, (s, _)| a | s.set);
                let loose = g.terms().iter().any(|(m, c)| {
                    matches!(m.as_slice(), [(s, 1)] if s.class == whole
                        && s.set.count_ones() == 1
                        && s.set & masked == 0)
                        && *c != BitVec::one(w)
                        && *c != BitVec::ones(w)
                });
                if loose || Bits::from_linear(&g.expand_full(&n.classes), &n.classes).is_none() {
                    continue;
                }
                let e = finish(&g);
                if e != *nf && !alts.contains(&e) && !bitwise.contains(&e) {
                    bitwise.push(e);
                }
            }
        }
    }
    // Bitwise forms first: they render cheaply, and the others may not all fit the budget.
    let rest: Vec<Poly> = alts
        .split_off(known)
        .into_iter()
        .filter(|a| !bitwise.contains(a))
        .collect();
    let mut out = bitwise;
    out.extend(rest);
    out.retain(|a| a != nf);
    Ok(out)
}

/// `p` (of degree at most 1) with a variable of atom `a`'s definition `d` read through the
/// atom: `v = α⁻¹·(a − (d − α·v))` for a variable `v` that `d` reads alone, with an odd
/// coefficient `α`, and that `p` reads alone, both unmasked (`whole`: `FULL`, or the only
/// class). A masked `v & M` is not `α⁻¹·((a & M) − …)`: the identity holds for the whole
/// atom only. `None` when there is none or nothing changes.
fn eliminate_var(p: &Poly, a: u32, d: &Poly, vars: u32, whole: u16) -> Option<Poly> {
    let w = p.width();
    if p.degree() > 1 || d.degree() > 1 || a >= 64 {
        return None;
    }
    let (m, alpha) = d.terms().iter().find(|(m, c)| {
        matches!(m.as_slice(), [(s, 1)] if s.set.count_ones() == 1
            && s.set.trailing_zeros() < vars
            && (s.class == whole || s.class == FULL)
            && p.terms().contains_key(*m))
            && c.bit(0) == Some(true)
    })?;
    let v = m[0].0;
    // v = α⁻¹·(a − (d − α·v)).
    let mut rest = d.clone();
    rest.add_term(
        m.clone(),
        &BitVec::un_unchecked(crate::ops::UnOp::Neg, alpha),
    );
    let r = Poly::sym(
        w,
        Sym {
            set: 1 << a,
            class: v.class,
        },
    )
    .sub(&rest)
    .scale(&poly::odd_inverse(alpha));
    let out = p.replace(v, &r, 4096)?;
    (out != *p).then_some(out)
}

/// The values of `exprs` at the refutation sample of `p` (lanes of 64 bits: `None` wider).
fn sample_values(
    p: &MbaExpr,
    exprs: &[&MbaExpr],
    work: &mut Steps,
) -> Result<Option<Vec<Vec<u64>>>, Decline> {
    use certify::Meter;
    let points = certify::sample_points(p.vars(), &[p], p.key()[0]);
    let inputs: Vec<Vec<u64>> = (0..p.vars().len())
        .map(|v| {
            points
                .iter()
                .map(|pt| pt[v].limbs().first().copied().unwrap_or(0))
                .collect()
        })
        .collect();
    let mut out = Vec::with_capacity(exprs.len());
    for e in exprs {
        let Some(prog) = crate::mba::batch::Program::new(e, false) else {
            return Ok(None);
        };
        if prog.widest() > 64 {
            return Ok(None);
        }
        let units = (prog.len() * points.len()) as u64;
        work.charge(units.div_ceil(EVALS_PER_STEP))
            .map_err(|()| Decline::Exhausted)?;
        let mut regs: Vec<Vec<u64>> = Vec::new();
        prog.run(&mut regs, &inputs, points.len());
        match regs.get(prog.root()) {
            Some(r) => out.push(r[..points.len()].to_vec()),
            None => return Ok(None),
        }
    }
    Ok(Some(out))
}

/// Atoms that depend on each other so that some patterns of their bits never occur (`y + 1`
/// and `(y + y)` of `~y` are never both 1 outside `y`): a degree-≤1 form whose values follow,
/// in every class over the patterns that occur there at the sample, a function of fewer atoms
/// is that function (with the constant the dropped atoms leave in each class), used once a
/// certificate proves the two equal. So `((y + 1) & (~y + ~y)) | y | x` is `x | y`. Atoms
/// defined by normal forms are dropped first, greedily.
fn drop_dependent_atoms(
    p: &MbaExpr,
    nf: &mut Poly,
    classes: &Classes,
    atoms: &[Def],
    atom_exprs: &[MbaExpr],
    work: &mut Steps,
    tally: &mut NfStats,
) -> Result<(), Decline> {
    let w = nf.width();
    if nf.degree() > 1 || w.bits() > 64 {
        return Ok(());
    }
    let set = nf.atoms();
    let u: Vec<u32> = (0..64).filter(|&a| set >> a & 1 == 1).collect();
    let derived = |a: u32| {
        matches!(
            atoms.get(a as usize),
            Some(Def::Form(_) | Def::Complement(_))
        )
    };
    if u.len() < 2 || u.len() > 5 || !u.iter().any(|&a| derived(a)) {
        return Ok(());
    }
    // The patterns of the atoms' bits at the sample, per class.
    let exprs: Vec<&MbaExpr> = u
        .iter()
        .filter_map(|&a| atom_exprs.get(a as usize))
        .collect();
    if exprs.len() != u.len() {
        return Ok(());
    }
    let Some(vals) = sample_values(p, &exprs, work)? else {
        return Ok(());
    };
    let k = u.len();
    let n = classes.len();
    let class_of: Vec<usize> = (0..w.bits())
        .map(|j| {
            (0..n)
                .find(|&c| classes.mask(c).bit(j) == Some(true))
                .unwrap_or(0)
        })
        .collect();
    let mut seen = vec![0u64; n];
    for (pt, _) in vals[0].iter().enumerate() {
        for j in 0..w.bits() {
            let e = vals
                .iter()
                .enumerate()
                .fold(0u64, |e, (i, col)| e | ((col[pt] >> j) & 1) << i);
            seen[class_of[usize::from(j)]] |= 1 << e;
        }
    }
    let all = if 1u64 << k == 64 {
        u64::MAX
    } else {
        (1u64 << (1u64 << k)) - 1
    };
    if seen.iter().all(|&s| s == all) {
        return Ok(());
    }
    // Per class, the form's value at each pattern (the constant apart): the sum of the
    // coefficients of the conjunctions inside it, modulo the class's precision.
    let index = |s: u64| {
        (0..k)
            .filter(|&i| s >> u[i] & 1 == 1)
            .fold(0usize, |q, i| q | 1 << i)
    };
    let q = nf.expand_full(classes);
    let mut val = vec![vec![BitVec::zero(w); 1 << k]; n];
    for (m, c) in q.terms() {
        match m.as_slice() {
            [] => {}
            [(s, 1)] => {
                let v = &mut val[usize::from(s.class).min(n - 1)][index(s.set)];
                *v = BitVec::bin_unchecked(crate::ops::BinOp::Add, v, c);
            }
            _ => return Ok(()),
        }
    }
    let prec = |c: usize| {
        crate::facts::known::low_mask(w, u32::from(w.bits()) - u32::from(classes.low(c)))
    };
    for (c, v) in val.iter_mut().enumerate() {
        for b in 0..k {
            for q in 0..1usize << k {
                if q >> b & 1 == 1 {
                    v[q] = BitVec::bin_unchecked(crate::ops::BinOp::Add, &v[q], &v[q ^ 1 << b]);
                }
            }
        }
        let lm = prec(c);
        for x in v.iter_mut() {
            *x = crate::facts::known::bv_and(x, &lm);
        }
    }
    // Greedily, atoms the values over the occurring patterns do not depend on, in any class.
    let mut keep: Vec<usize> = (0..k).collect();
    let mut order: Vec<usize> = (0..k).collect();
    order.sort_by_key(|&i| !derived(u[i]));
    let mut dropped = false;
    for i in order {
        let independent = (0..n).all(|c| {
            (0..1usize << k).all(|q| {
                let r = q ^ 1 << i;
                seen[c] >> q & 1 == 0 || seen[c] >> r & 1 == 0 || val[c][q] == val[c][r]
            })
        });
        if independent && keep.len() > 1 {
            keep.retain(|&x| x != i);
            for c in 0..n {
                // Read the dropped atom where a pattern occurs, else as 0.
                for q in 0..1usize << k {
                    let r = q ^ 1 << i;
                    if q >> i & 1 == 0 && seen[c] >> q & 1 == 0 && seen[c] >> r & 1 == 1 {
                        val[c][q] = val[c][r];
                    }
                    if q >> i & 1 == 1 {
                        val[c][q] = val[c][r];
                    }
                }
                for q in 0..1usize << k {
                    if seen[c] >> q & 1 == 1 {
                        seen[c] |= 1 << (q & !(1 << i));
                    }
                }
            }
            dropped = true;
        }
    }
    if !dropped {
        return Ok(());
    }
    // The new part over the atoms kept, class by class: Möbius over their patterns (the dropped
    // ones at 0).
    let kk = keep.len();
    let mut fresh = Poly::constant(nf.konst());
    for (c, v) in val.iter().enumerate() {
        let mut coef: Vec<BitVec> = (0..1usize << kk)
            .map(|q| {
                let full = keep
                    .iter()
                    .enumerate()
                    .fold(0usize, |f, (t, &i)| f | ((q >> t) & 1) << i);
                v[full]
            })
            .collect();
        for b in 0..kk {
            for q in 0..1usize << kk {
                if q >> b & 1 == 1 {
                    coef[q] =
                        BitVec::bin_unchecked(crate::ops::BinOp::Sub, &coef[q], &coef[q ^ 1 << b]);
                }
            }
        }
        // What the dropped atoms contribute where the kept ones are all 0: a constant in the
        // class's positions.
        fresh.add_term(
            Vec::new(),
            &BitVec::bin_unchecked(crate::ops::BinOp::Mul, &coef[0], classes.mask(c)),
        );
        for (q, x) in coef.iter().enumerate().skip(1) {
            let s = keep
                .iter()
                .enumerate()
                .filter(|&(t, _)| q >> t & 1 == 1)
                .fold(0u64, |s, (_, &i)| s | 1 << u[i]);
            fresh.add_term(
                vec![(
                    poly::Sym {
                        set: s,
                        class: c as u16,
                    },
                    1,
                )],
                x,
            );
        }
    }
    fresh.reduce_core(classes);
    if fresh == *nf {
        return Ok(());
    }
    // The proof: both as expressions over the atoms' renderings.
    let render = |f: &Poly| -> Option<MbaExpr> {
        let mut r = Render::new(p.vars().to_vec(), w, classes, atom_exprs, u64::MAX);
        let mut sum = render::Sum {
            terms: Vec::new(),
            konst: Some(f.konst()),
        };
        for (m, c) in f.terms() {
            if !m.is_empty() {
                sum.terms.push((r.mono(m)?, *c));
            }
        }
        let root = r.sum(&sum);
        r.b.finish(root)
    };
    let (Some(old), Some(new)) = (render(nf), render(&fresh)) else {
        return Ok(());
    };
    let report = certify_within(&old, &new, work);
    tally.certificates.record(&report);
    if report.verdict == Verdict::Proved {
        *nf = fresh;
    }
    Ok(())
}

/// The most factors of the input's products whose sums and differences are tried as factors.
const FACTORS_PAIRED: usize = 6;

/// The most atom relations `n − d` [`more_forms`] combines looking for a bitwise function.
const BITWISE_RELATIONS: usize = 5;

/// The most conjunctions of atoms a question tries to prove zero.
const NULL_CONJUNCTIONS: usize = 8;

/// Drops conjunctions of atoms that are zero although no reduction shows it, because the atoms
/// depend on each other (`(y + y) & y & −y`: no bit of `y` both follows a set bit and has none
/// below it). A term whose conjunction is zero at the refutation sample is tried, and dropped
/// only when a certificate proves the conjunction (under its class's mask) zero; `nulls` gets
/// the proved ones.
fn prune_null_conjunctions(
    p: &MbaExpr,
    nf: &mut Poly,
    classes: &Classes,
    atom_exprs: &[MbaExpr],
    nulls: &mut Vec<poly::Sym>,
    work: &mut Steps,
    tally: &mut NfStats,
) -> Result<(), Decline> {
    use certify::Meter;
    let w = nf.width();
    let bits = w.bits();
    if bits > 64 {
        return Ok(());
    }
    let mask64 = if bits >= 64 {
        u64::MAX
    } else {
        (1u64 << bits) - 1
    };
    let points = certify::sample_points(p.vars(), &[p], p.key()[0]);
    let inputs: Vec<Vec<u64>> = (0..p.vars().len())
        .map(|v| {
            points
                .iter()
                .map(|pt| pt[v].limbs().first().copied().unwrap_or(0))
                .collect()
        })
        .collect();
    // An atom's values at the sample, from its rendering.
    let atom_values = |a: u32, work: &mut Steps| -> Result<Option<Vec<u64>>, Decline> {
        let Some(e) = atom_exprs.get(a as usize) else {
            return Ok(None);
        };
        let Some(prog) = crate::mba::batch::Program::new(e, false) else {
            return Ok(None);
        };
        if prog.widest() > 64 {
            return Ok(None);
        }
        let units = (prog.len() * points.len()) as u64;
        work.charge(units.div_ceil(EVALS_PER_STEP))
            .map_err(|()| Decline::Exhausted)?;
        let mut regs: Vec<Vec<u64>> = Vec::new();
        prog.run(&mut regs, &inputs, points.len());
        Ok(regs.get(prog.root()).map(|r| r[..points.len()].to_vec()))
    };
    let cand: Vec<(poly::Mono, BitVec)> = nf
        .terms()
        .iter()
        .filter(|(m, _)| matches!(m.as_slice(), [(s, 1)] if s.set.count_ones() >= 2))
        .map(|(m, c)| (m.clone(), *c))
        .take(NULL_CONJUNCTIONS)
        .collect();
    if cand.is_empty() {
        return Ok(());
    }
    let mut zero = MbaExpr::new(p.vars().to_vec());
    zero.push(MOp::Const(BitVec::zero(w)), &[])
        .map_err(|_| Decline::Unsupported("internal: zero"))?;
    for (m, c) in cand {
        let sym = m[0].0;
        let mut vals: Option<Vec<u64>> = None;
        for a in (0..64u32).filter(|&a| sym.set >> a & 1 == 1) {
            let Some(v) = atom_values(a, work)? else {
                return Ok(());
            };
            vals = Some(match vals {
                None => v,
                Some(acc) => acc.iter().zip(&v).map(|(x, y)| x & y).collect(),
            });
        }
        let class_mask = classes
            .mask(usize::from(sym.class))
            .limbs()
            .first()
            .copied();
        let masked = |x: &u64| x & class_mask.unwrap_or(u64::MAX) & mask64;
        if !vals.is_some_and(|v| v.iter().all(|x| masked(x) == 0)) {
            continue;
        }
        let mut r = Render::new(p.vars().to_vec(), w, classes, atom_exprs, u64::MAX);
        let Some(root) = r.mono(&m) else {
            continue;
        };
        let Some(e) = r.b.finish(root) else {
            continue;
        };
        let report = certify_within(&e, &zero, work);
        tally.certificates.record(&report);
        if report.verdict == Verdict::Proved {
            nf.add_term(m, &BitVec::un_unchecked(crate::ops::UnOp::Neg, &c));
            nulls.push(sym);
            tally.null_parts += 1;
        }
    }
    Ok(())
}

/// Drops null parts the reductions miss. Every null polynomial of degree at most `d` in one
/// variable has coefficients divisible by `2^(W − v₂(d!))`; the terms of `nf` whose coefficients
/// are are tried as one part, then grouped by the atoms they mention, and a part is dropped
/// only when a certificate proves it zero.
fn prune_null(
    p: &MbaExpr,
    nf: &mut Poly,
    classes: &Classes,
    atom_exprs: &[MbaExpr],
    work: &mut Steps,
    tally: &mut NfStats,
) -> Result<(), Decline> {
    let w = nf.width();
    let d = nf.degree();
    let v = d - d.count_ones();
    let t = u32::from(w.bits()).saturating_sub(v);
    let divisible = |c: &BitVec| crate::facts::known::trailing_zeros(c) >= t;
    let cand: Vec<(poly::Mono, BitVec)> = nf
        .terms()
        .iter()
        .filter(|(m, c)| !m.is_empty() && divisible(c))
        .map(|(m, c)| (m.clone(), *c))
        .collect();
    if !cand.iter().any(|(m, _)| poly::degree(m) >= 2) {
        return Ok(());
    }
    // The whole candidate first, then groups by the atoms their monomials mention.
    let mut groups: Vec<Vec<(poly::Mono, BitVec)>> = vec![cand.clone()];
    let mut by_atoms: std::collections::BTreeMap<u64, Vec<(poly::Mono, BitVec)>> =
        std::collections::BTreeMap::new();
    for (m, c) in &cand {
        let atoms = m.iter().fold(0u64, |a, (s, _)| a | s.set);
        by_atoms.entry(atoms).or_default().push((m.clone(), *c));
    }
    if by_atoms.len() > 1 {
        groups.extend(by_atoms.into_values());
    }
    let mut zero = MbaExpr::new(p.vars().to_vec());
    zero.push(MOp::Const(BitVec::zero(w)), &[])
        .map_err(|_| Decline::Unsupported("internal: zero"))?;
    for g in groups {
        let present = g.iter().all(|(m, c)| nf.terms().get(m) == Some(c));
        if !present || !g.iter().any(|(m, _)| poly::degree(m) >= 2) {
            continue;
        }
        let mut r = Render::new(p.vars().to_vec(), w, classes, atom_exprs, u64::MAX);
        let mut sum = render::Sum::default();
        for (m, c) in &g {
            let Some(t) = r.mono(m) else {
                return Ok(());
            };
            sum.terms.push((t, *c));
        }
        let root = r.sum(&sum);
        let Some(e) = r.b.finish(root) else {
            return Ok(());
        };
        let report = certify_within(&e, &zero, work);
        tally.certificates.record(&report);
        if report.verdict == Verdict::Proved {
            for (m, c) in &g {
                nf.add_term(m.clone(), &BitVec::un_unchecked(crate::ops::UnOp::Neg, c));
            }
            tally.null_parts += 1;
        }
    }
    Ok(())
}

/// The candidates for a normal form, rendered into `r`.
fn candidates(r: &mut Render<'_>, nf: &Poly, factors: &[Poly]) -> Vec<u32> {
    r.poly(nf, factors, 0)
}

/// A normal form's cheapest rendering, and a cheaper synthesized one no certificate decided.
#[derive(Default)]
struct Rendered {
    exact: Option<(render::Cost, MbaExpr)>,
    unproved: Option<(render::Cost, MbaExpr)>,
}

/// The cheapest rendering of `n`: rendered, then again with the factors the best candidate
/// multiplies, until none is new (a few rounds), so the answer is as good as the factors its
/// own products offer. Rendering cut short by the budget is [`Decline::Exhausted`]: what it
/// found need not be the cheapest, and nothing is left to certify it.
fn best_rendering(
    p: &MbaExpr,
    n: &Normal,
    bar: u32,
    work: &mut Steps,
    tally: &mut NfStats,
) -> Result<Rendered, Decline> {
    use certify::Meter;
    let mut factors = n.factors.clone();
    let mut best: Option<(render::Cost, MbaExpr)> = None;
    let mut unproved = None;
    // The other forms of the function (atoms reused, variables eliminated, zero added):
    // rendered in the first round, with the input's factors.
    let more = more_forms(n, work)?;
    tally.reused += u64::from(n.alts.is_empty() && !more.is_empty());
    for round in 0..3 {
        let mut r =
            Render::new(p.vars().to_vec(), n.w, &n.classes, &n.atom_exprs, work.left).with_bar(bar);
        let mut cands = candidates(&mut r, &n.nf, &factors);
        // The normal form renders within the budget or not at all (nothing would say the best
        // was seen); what comes after only adds candidates, so running short there only stops
        // it: the other forms each take at most half of what is left while a quarter is, and a
        // later round cut short is dropped.
        if r.exhausted() {
            if round == 0 {
                return Err(Decline::Exhausted);
            }
            break;
        }
        if round == 0 {
            let cap = r.limit();
            for alt in n.alts.iter().chain(&more) {
                let left = cap.saturating_sub(r.work);
                if left < cap / 4 {
                    break;
                }
                r.set_limit(r.work + left / 2);
                cands.extend(candidates(&mut r, alt, &factors));
                r.set_limit(cap);
                r.work = r.work.min(cap);
            }
        }
        // Synthesis does not depend on the factors: the first round is enough.
        if round == 0 && n.synthesis && !r.hopeless(n.nf.atoms()) {
            let bar = r.best(&cands).map(|b| r.b.cost(b));
            match r.synthesize(&n.nf, bar) {
                Some(render::Hit::Exact(x)) => cands.push(x),
                Some(render::Hit::Unproved(x)) => {
                    unproved = r.b.finish(x).map(|e| (r.b.cost(x), e));
                }
                None => {}
            }
            add_synth(tally, &r.synth);
        }
        tally.candidates += r.built;
        if r.exhausted() {
            if round == 0 {
                return Err(Decline::Exhausted);
            }
            break;
        }
        work.charge(r.work.max(1))
            .map_err(|()| Decline::Exhausted)?;
        let Some(b) = r.best(&cands) else {
            break;
        };
        let cost = r.b.cost(b);
        if best.as_ref().is_none_or(|(c, _)| cost < *c) {
            let Some(e) = r.b.finish(b) else {
                return Err(Decline::Unsupported("internal: rendering"));
            };
            best = Some((cost, e));
        }
        let more: Vec<Poly> = r
            .factors_of(b)
            .into_iter()
            .filter(|f| !factors.contains(f))
            .collect();
        if more.is_empty() {
            break;
        }
        factors.extend(more);
    }
    // Undecided hits count only where they beat every exact rendering.
    let unproved = unproved.filter(|(c, _)| best.as_ref().is_none_or(|(b, _)| c < b));
    Ok(Rendered {
        exact: best,
        unproved,
    })
}

fn run(
    p: &MbaExpr,
    opts: &NfOptions,
    budget: &MbaBudget,
    tally: &mut NfStats,
) -> Result<MbaAnswer, Decline> {
    let n = normalize(p, opts, budget, tally)?;
    let input_cost = n.input_cost;
    let mut work = Steps::new(n.work.left);
    // Only renderings smaller than the question can be answers.
    let rendered = best_rendering(p, &n, input_cost, &mut work, tally)?;
    let mut exact = rendered.exact.filter(|(c, _)| c.0 < input_cost);
    if let Some((mut cost, mut answer)) = exact.take() {
        // A fixed point: the answer, normalized again (its own constants may give coarser bit
        // classes, its own products other factors), until that renders nothing smaller.
        // Solving the answer again then finds nothing smaller either.
        for _ in 0..3 {
            let mut scratch = NfStats::default();
            let again = normalize(
                &answer,
                opts,
                &MbaBudget::default().with_steps(work.left),
                &mut scratch,
            )
            .and_then(|m| {
                let mut w2 = Steps::new(m.work.left);
                // Ties in nodes may still weigh less.
                let r = best_rendering(&answer, &m, cost.0 + 1, &mut w2, &mut scratch);
                let spent = work.left - w2.left.min(work.left);
                work = Steps::new(work.left - spent);
                r.map(|r| (m.halved, r))
            });
            tally.candidates += scratch.candidates;
            // Running short only ends the search.
            match again.map(|(halved, r)| (halved, r.exact)) {
                Ok((halved, Some((c, e)))) if c < cost => {
                    // Halves the question's own normal form did not take lead where the
                    // certificates do not follow (`(x + x) & (y + y)` as `2·(x & y)` against
                    // `(y·a + b)·c | …`, the question): the answer stays within their reach.
                    if halved && !n.halved {
                        break;
                    }
                    cost = c;
                    answer = e;
                }
                _ => break,
            }
        }
        exact = Some((cost, answer));
    }
    // A synthesized form no certificate decided, cheaper than every exact answer: only with a
    // certificate against the input, else on the refutation sample as a sampled answer.
    if let Some((c, hit)) = rendered.unproved
        && c.0 < input_cost
        && exact.as_ref().is_none_or(|(e, _)| c < *e)
    {
        let report = certify_within(p, &hit, &mut work);
        tally.certificates.record(&report);
        match report.verdict {
            Verdict::Proved => {
                return Ok(MbaAnswer::Simplified {
                    expr: hit,
                    claim: Claim::Proved,
                });
            }
            Verdict::Refuted => tally.synth_refuted += 1,
            _ => {
                let seed = crate::hash::combine(p.key()[0], hit.key()[1]);
                let points = certify::sample_points(p.vars(), &[p, &hit], seed);
                if certify::refute(p, &hit, &points).is_none() {
                    tally.synth_sampled += 1;
                    return Ok(MbaAnswer::Simplified {
                        expr: hit,
                        claim: Claim::Sampled,
                    });
                }
                tally.synth_refuted += 1;
            }
        }
    }
    let Some((_, answer)) = exact else {
        return Ok(MbaAnswer::NoSimpler);
    };
    // Exact by construction; a caller that proves answers itself asked for no evidence.
    if !budget.evidence {
        return Ok(MbaAnswer::Simplified {
            expr: answer,
            claim: Claim::Unverified,
        });
    }
    // The self-check: the answer against the input, by a certificate (within what is left),
    // else at the refutation sample only.
    let report = certify_within(p, &answer, &mut work);
    tally.certificates.record(&report);
    match report.verdict {
        Verdict::Proved => Ok(MbaAnswer::Simplified {
            expr: answer,
            claim: Claim::Proved,
        }),
        Verdict::Refuted => {
            tally.declined_internal += 1;
            Err(Decline::Unsupported(
                "internal: the self-check refuted the answer",
            ))
        }
        _ => {
            let seed = crate::hash::combine(p.key()[0], answer.key()[1]);
            let points = certify::sample_points(p.vars(), &[p, &answer], seed);
            if certify::refute(p, &answer, &points).is_some() {
                tally.declined_internal += 1;
                return Err(Decline::Unsupported(
                    "internal: the sample refuted the answer",
                ));
            }
            Ok(MbaAnswer::Simplified {
                expr: answer,
                claim: Claim::Sampled,
            })
        }
    }
}

/// For tests: the normal form of `p` rendered term by term (each monomial with its
/// coefficient), and every candidate rendering (also of the forms with atoms reused).
#[cfg(test)]
pub(crate) fn inspect(p: &MbaExpr, opts: &NfOptions) -> Option<(MbaExpr, Vec<MbaExpr>)> {
    let mut tally = NfStats::default();
    let n = normalize(
        p,
        opts,
        &MbaBudget::default().with_steps(u64::MAX),
        &mut tally,
    )
    .ok()?;
    let mut r = Render::new(p.vars().to_vec(), n.w, &n.classes, &n.atom_exprs, u64::MAX);
    let mut sum = render::Sum {
        terms: Vec::new(),
        konst: Some(n.nf.konst()),
    };
    for (m, c) in n.nf.terms() {
        if !m.is_empty() {
            let t = r.mono(m)?;
            sum.terms.push((t, *c));
        }
    }
    let naive = r.sum(&sum);
    let naive = r.b.finish(naive)?;
    let mut cands = candidates(&mut r, &n.nf, &n.factors);
    for alt in &n.alts {
        cands.extend(candidates(&mut r, alt, &n.factors));
    }
    let cands: Option<Vec<MbaExpr>> = cands.iter().map(|&c| r.b.finish(c)).collect();
    Some((naive, cands?))
}
