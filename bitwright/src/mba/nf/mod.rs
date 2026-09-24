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
use self::classes::Classes;
use self::poly::Poly;
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
    /// 16 atoms, 16 classes, 1024 monomials, degree 16; 1024 answers remembered; synthesis on.
    fn default() -> Self {
        NfOptions {
            max_atoms: 16,
            max_classes: 16,
            max_terms: 1024,
            max_degree: 16,
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
    /// Bitwise operations with a constant read as arithmetic: the constant reads only low bits
    /// of the other operand that are known (`−2·(x & 1) | 1` is `1 − 2·(x & 1)`).
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
type MemoKey = ([u64; 2], u64);

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
            "bitwright.nf.v2;atoms={};classes={};terms={};degree={};synth={}",
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
        let key = (p.key(), budget.steps);
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
                if *claim == Claim::Proved {
                    tally.proved += 1;
                } else {
                    tally.sampled += 1;
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
    /// Per atom: the normal form it is rendered from (for `Def::Form` and `Def::Shift`).
    atom_nf: Vec<Option<Poly>>,
    /// Atoms by what identifies them.
    atom_of: HashMap<AtomKey, u32>,
    /// Normal forms of the operands of products: factors worth trying when rendering.
    factors: Vec<Poly>,
}

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
                // Arithmetic that is secretly a bitwise function is read as one; otherwise it
                // is an atom, identified by its normal form.
                let key = self.key_form(&p);
                if key.degree() <= 1 {
                    self.charge((key.len() as u64) << key.atoms().count_ones().min(12))?;
                    if let Some(f) = Bits::from_linear(&key, &self.classes) {
                        return Ok(f);
                    }
                }
                let a = self.atom(AtomKey::Form(key.clone()), Def::Form(i), Some(key), tally)?;
                Ok(Bits::atom(n, a))
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

    /// Remembers the normal form of a product's operand: rendering tries it as a factor.
    fn note_factor(&mut self, f: &Poly) {
        if f.degree() >= 1 && f.len() <= 64 && self.factors.len() < 16 && !self.factors.contains(f)
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
                    let (x, y) = (self.poly(a, tally)?, self.poly(b, tally)?);
                    let size = (x.len() as u64).saturating_mul(y.len() as u64);
                    let max = u64::from(self.opts.max_terms);
                    if size > max.saturating_mul(4)
                        || x.degree() + y.degree() > self.opts.max_degree
                    {
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
    classes: Classes,
    nf: Poly,
    /// The same function with atoms standing for their definitions where these appear
    /// arithmetically (rendered too; the cheapest wins).
    alts: Vec<Poly>,
    atom_exprs: Vec<MbaExpr>,
    factors: Vec<Poly>,
    input_cost: u32,
    work: Steps,
    synthesis: bool,
}

fn normalize(
    p: &MbaExpr,
    opts: &NfOptions,
    budget: &MbaBudget,
    tally: &mut NfStats,
) -> Result<Normal, Decline> {
    let Some(w) = p.width() else {
        return Err(Decline::Unsupported("empty"));
    };
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
        work.charge(nodes.len() as u64)
            .map_err(|()| Decline::Exhausted)?;
    }
    // Constants read by bitwise operators define the bit classes.
    let mut consts: Vec<BitVec> = Vec::new();
    for (i, n) in nodes.iter().enumerate() {
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
    let Some(classes) = Classes::new(w, &consts, opts.max_classes as usize) else {
        tally.declined_classes += 1;
        return Err(Decline::Unsupported("too many bit classes"));
    };
    let (canon, input_cost) = canonical(p, &live);
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
    // Normal forms as rendered: unmasked symbols wherever the classes allow (the same
    // function), then the one-position rule.
    let finish = |f: &Poly| {
        let mut f = f.clone();
        f.reduce_core(&pass.classes);
        let mut f = f.declass(&pass.classes, DECLASS_LIMIT);
        f.single_positions(&pass.classes);
        f.reduce_core(&pass.classes);
        f
    };
    let factors: Vec<Poly> = pass.factors.iter().map(finish).collect();
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
            Def::Form(i) | Def::Shift(_, i) => {
                let form = finish(pass.atom_nf[a].as_ref().ok_or_else(internal)?);
                let mut r = Render::new(
                    p.vars().to_vec(),
                    w,
                    &pass.classes,
                    &atom_exprs[..a],
                    work.left,
                );
                let mut cands = candidates(&mut r, &form, &factors);
                if let Some(v) = verbatim(p, i)
                    && let Some(root) = r.b.import(&v)
                {
                    cands.push(root);
                }
                if opts.synthesis {
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
    let mut alt: Option<Poly> = None;
    let mut alt_len: Option<usize> = None;
    let mut reused = false;
    for (a, def) in pass.atoms.iter().enumerate() {
        let (Def::Form(_), Some(d)) = (def, pass.atom_nf[a].as_ref()) else {
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
        classes: pass.classes,
        nf,
        alts,
        atom_exprs,
        factors,
        input_cost,
        work,
        synthesis: opts.synthesis,
    })
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
    work: &mut Steps,
    tally: &mut NfStats,
) -> Result<Rendered, Decline> {
    use certify::Meter;
    let mut factors = n.factors.clone();
    let mut best: Option<(render::Cost, MbaExpr)> = None;
    let mut unproved = None;
    for round in 0..3 {
        let mut r = Render::new(p.vars().to_vec(), n.w, &n.classes, &n.atom_exprs, work.left);
        let mut cands = candidates(&mut r, &n.nf, &factors);
        // The forms with atoms reused: once, with the input's factors.
        if round == 0 {
            for alt in &n.alts {
                cands.extend(candidates(&mut r, alt, &factors));
            }
        }
        // Synthesis does not depend on the factors: the first round is enough.
        if round == 0 && n.synthesis {
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
            return Err(Decline::Exhausted);
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
    let rendered = best_rendering(p, &n, &mut work, tally)?;
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
                let r = best_rendering(&answer, &m, &mut w2, &mut scratch);
                let spent = work.left - w2.left.min(work.left);
                work = Steps::new(work.left - spent);
                r
            });
            tally.candidates += scratch.candidates;
            match again.map(|r| r.exact) {
                Ok(Some((c, e))) if c < cost => {
                    cost = c;
                    answer = e;
                }
                Err(Decline::Exhausted) => return Err(Decline::Exhausted),
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
