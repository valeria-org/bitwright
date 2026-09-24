//! Exact certificates for MBA equalities: finite evaluation tests, each complete for its
//! fragment (design §9). A certificate compares two expressions at a set of points chosen so
//! that agreement there proves agreement everywhere:
//!
//! - **Signature.** Linear MBA with only 0 and all-ones constants inside bitwise parts is
//!   determined by its values at the 2^t corners where every variable is 0 or all-ones.
//! - **Sparse** (single-position for degree 1). A *polynomial MBA* is built with `+ − ·`,
//!   negation, constant left shifts and constants over bitwise functions of the variables
//!   (`& | ^ ~` over variables and constants). Its syntactic degree `d` is the largest number of
//!   bitwise factors (variables count as bitwise) in a product. Writing each variable as
//!   `Σ_j 2^j·x[j]` makes the difference of two such expressions an integer polynomial in the
//!   `t·W` input bits (reduction mod 2^W is a ring homomorphism, so carries need no special
//!   care); after `b² = b` it is multilinear, and each monomial touches at most `d` bit
//!   positions, one per factor. A multilinear function over a commutative ring has a unique
//!   representation, and Möbius inversion recovers each coefficient from its values at points
//!   supported inside the coefficient's monomial. So the two expressions are equal if and only
//!   if they agree at every point where the set bits of all variables together lie in at most
//!   `d` positions: `Σ_{k≤d} C(W,k)·(2^t − 1)^k` points.
//! - **Grid.** Without bitwise operators, two polynomials of degree at most `d_i` in variable
//!   `i` are equal if they agree on `Π_i {0..d_i}`: forward differences there give `α!·h_α` for
//!   the falling-factorial coefficients `h_α`, and `h_α·Π(x_i)_{α_i}` vanishes when `α!·h_α`
//!   does, because `Π(x_i)_{α_i}` is a multiple of `α!`.
//! - **Exhaustive.** Every assignment, when the variables total at most 20 bits.
//! - **Compositional.** Subterms outside the polynomial fragment (right shifts, casts,
//!   arithmetic read by a bitwise operator) become *atoms*, shared between both sides by
//!   structure, by congruence (`f(a) = f(b)` when `a = b`), and by proofs of their definitions.
//!   The two *skeletons* are then compared by one of the tests above, treating atoms as
//!   independent variables: an identity for independent atoms holds for any values of them.
//!   A skeleton that differs proves nothing (the atoms may be dependent): the answer is
//!   unknown, never refuted.
//! - **Known bits.** When those leave the question open, `x op k` (`op` bitwise, `k` a
//!   constant) is read as arithmetic wherever the known bits of `x` cover the bits `k` is 1
//!   at, or those it is 0 at: equal functions, so a verdict on them is one on the question.
//! - **Cases.** Then a variable is split over a few of its bits: those both sides read it
//!   through narrow masks at, or the low bits bitwise operations with constants read. The cases
//!   cover every input, and each is proved on its own.
//!
//! Every test is sized before it runs and charged a block at a time; one over the budget is
//! not run. `Refuted` always comes with a concrete input where the two sides differ.

use std::collections::HashMap;

use super::batch::{BLOCK, Kind, Lane, Program, Wide};
use super::expr::{MNode, MOp, MbaExpr};
use super::solve::Verdict;
use crate::engine::CertStats;
use crate::ops::{BinOp, UnOp};
use crate::{BitVec, Width};

/// The most points one test evaluates, whatever the budget.
pub(crate) const MAX_POINTS: u64 = 1 << 24;

/// The most effort one test may take, whatever the budget: points × nodes × the cost of a lane
/// (1 up to 64 bits, 2 up to 128, 8 above). A larger test is not run and is a stable decline, so
/// whether a node is final never depends on the budget; a test within this cap but over what
/// is left of the budget leaves the node non-final.
pub(crate) const MAX_EFFORT: u64 = 1 << 25;

/// Exhaustive evaluation is a test up to this many variable bits.
pub(crate) const EXHAUSTIVE_BITS: u32 = 20;

/// The signature test takes at most this many variables.
const SIGNATURE_VARS: usize = 16;

/// Points of the refutation sample.
pub(crate) const SAMPLE_POINTS: usize = 64;

/// The most proof attempts per atom when atoms are paired by their definitions.
const PAIR_TRIES: usize = 4;

/// The most bits of one variable a split enumerates (at most `2^SPLIT_BITS` cases).
const SPLIT_BITS: u32 = 4;

/// How deep splits nest (each one on another variable).
const SPLIT_DEPTH: u32 = 2;

/// The most work (node evaluations) one split spends on cases before it declines; like
/// [`MAX_EFFORT`], a decline that does not depend on the budget.
const SPLIT_EFFORT: u64 = MAX_EFFORT;

/// Work charged per node for reading known bits as arithmetic (a transfer of facts costs about
/// as much as evaluating a node at this many points).
pub(crate) const LOWER_COST: u64 = 64;

/// Work accounting for a certificate: units are node evaluations (one per node per point).
pub(crate) trait Meter {
    /// What a failed charge reports.
    type Err;
    /// Units left.
    fn left(&self) -> u64;
    /// Spends `units`.
    fn charge(&mut self, units: u64) -> Result<(), Self::Err>;
}

/// A meter over a plain count (a solver's or a prover's budget).
#[derive(Debug)]
pub(crate) struct Steps {
    pub(crate) left: u64,
    pub(crate) spent: u64,
}

impl Steps {
    pub(crate) fn new(left: u64) -> Steps {
        Steps { left, spent: 0 }
    }
}

impl Meter for Steps {
    type Err = ();
    fn left(&self) -> u64 {
        self.left
    }
    fn charge(&mut self, units: u64) -> Result<(), ()> {
        self.spent = self.spent.saturating_add(units);
        if units > self.left {
            self.left = 0;
            return Err(());
        }
        self.left -= units;
        Ok(())
    }
}

/// The test that decided.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
pub(crate) enum Cert {
    /// The corner signature (constant-free linear MBA).
    Signature,
    /// Single bit positions (degree ≤ 1).
    SingleBit,
    /// At most `d` bit positions (degree `d ≥ 2`).
    Sparse,
    /// The pure-polynomial grid.
    Grid,
    /// Every assignment.
    Exhaustive,
    /// Equal polynomials over symbols (see [`symbolic_equal`]).
    Symbolic,
    /// Bit-serial evaluation over every reachable carry state (see [`carries`]).
    Carries,
}

/// What a certificate found.
#[derive(Clone, Debug, PartialEq, Eq)]
pub(crate) struct Report {
    pub(crate) verdict: Verdict,
    /// The test that proved or refuted the equality (for a compositional proof, the one on the
    /// skeletons).
    pub(crate) cert: Option<Cert>,
    /// Atoms were abstracted.
    pub(crate) compositional: bool,
    /// Decided case by case over a few bits of one variable.
    pub(crate) split: bool,
    /// Decided after bitwise operations with constants that read only known bits were read
    /// as arithmetic.
    pub(crate) known_bits: bool,
    /// Points evaluated, over every test run.
    pub(crate) points: u64,
    /// A test was skipped for lack of budget (more budget might decide).
    pub(crate) over_budget: bool,
    /// Internal inconsistencies seen (a pairing that disagreed at a sample point); never
    /// expected.
    pub(crate) internal: u64,
    /// For `Refuted`: an input where the sides differ (one value per variable).
    pub(crate) counterexample: Option<Vec<BitVec>>,
    /// Node evaluations spent (by [`check`]).
    pub(crate) work: u64,
}

impl Report {
    pub(crate) fn new() -> Report {
        Report {
            verdict: Verdict::Unknown,
            cert: None,
            compositional: false,
            split: false,
            known_bits: false,
            points: 0,
            over_budget: false,
            internal: 0,
            counterexample: None,
            work: 0,
        }
    }
}

// ----- constant folding --------------------------------------------------------------------

/// The value of node `n` from its operands' values.
fn apply(n: &MNode, a: Option<&BitVec>, b: Option<&BitVec>) -> Option<BitVec> {
    let bin = |op: BinOp| Some(BitVec::bin_unchecked(op, a?, b?));
    match n.op {
        MOp::Const(v) => Some(v),
        MOp::Var(_) => None,
        MOp::Add => bin(BinOp::Add),
        MOp::Sub => bin(BinOp::Sub),
        MOp::Mul => bin(BinOp::Mul),
        MOp::And => bin(BinOp::And),
        MOp::Or => bin(BinOp::Or),
        MOp::Xor => bin(BinOp::Xor),
        MOp::Neg => Some(BitVec::un_unchecked(UnOp::Neg, a?)),
        MOp::Not => Some(BitVec::un_unchecked(UnOp::Not, a?)),
        MOp::Shl(k) | MOp::LShr(k) => {
            let a = a?;
            let kv = BitVec::wrapping_from_u64(a.width(), u64::from(k));
            let op = if matches!(n.op, MOp::Shl(_)) {
                BinOp::Shl
            } else {
                BinOp::LShr
            };
            Some(BitVec::bin_unchecked(op, a, &kv))
        }
        MOp::Zext => a?.zext(n.width).ok(),
        MOp::Sext => a?.sext(n.width).ok(),
        MOp::Trunc => a?.trunc(n.width).ok(),
    }
}

/// Per node: its value when it does not depend on any variable.
pub(crate) fn constants(nodes: &[MNode]) -> Vec<Option<BitVec>> {
    let mut cst: Vec<Option<BitVec>> = Vec::with_capacity(nodes.len());
    for n in nodes {
        let k = n.op.arity();
        let a = if k > 0 { cst[n.args[0] as usize] } else { None };
        let b = if k > 1 { cst[n.args[1] as usize] } else { None };
        let v = if matches!(n.op, MOp::Var(_)) || (k > 0 && a.is_none()) || (k > 1 && b.is_none()) {
            None
        } else {
            apply(n, a.as_ref(), b.as_ref())
        };
        cst.push(v);
    }
    cst
}

/// The nodes the root uses.
fn live(m: &MbaExpr) -> Vec<bool> {
    let nodes = m.nodes();
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

// ----- profiles --------------------------------------------------------------------------------

/// What the direct tests need to know about one expression.
#[derive(Clone, Debug)]
pub(crate) struct Profile {
    /// The root's width.
    pub(crate) width: Width,
    /// A polynomial MBA at one width: every live node and variable at the root's width, no
    /// right shift or cast of a non-constant, and every operand of `& | ^` a bitwise function
    /// of the variables (or a constant).
    pub(crate) poly: bool,
    /// Constants read by bitwise operators are 0 or all-ones.
    pub(crate) uniform: bool,
    /// Some `& | ^` of a non-constant.
    pub(crate) bitwise: bool,
    /// The syntactic degree (bitwise factors per product).
    pub(crate) degree: u32,
    /// Per variable: the degree in that variable (meaningful without bitwise operators).
    pub(crate) var_degree: Vec<u32>,
    /// Per variable: whether the root depends on it syntactically.
    pub(crate) used: Vec<bool>,
}

/// Degrees saturate here (any degree this high is far beyond what a test can afford).
const DEGREE_CAP: u32 = 1 << 12;

pub(crate) fn profile(m: &MbaExpr) -> Option<Profile> {
    let w = m.width()?;
    let nodes = m.nodes();
    let nv = m.vars().len();
    let live = live(m);
    let cst = constants(nodes);
    let mut local = vec![false; nodes.len()];
    let mut deg = vec![0u32; nodes.len()];
    let mut vdeg: Vec<Vec<u32>> = vec![Vec::new(); nodes.len()];
    let (mut poly, mut uniform, mut bitwise) = (true, true, false);
    let mut used = vec![false; nv];
    let zeros = vec![0u32; nv];
    for (i, n) in nodes.iter().enumerate() {
        if !live[i] {
            continue;
        }
        if cst[i].is_some() {
            local[i] = true;
            vdeg[i] = zeros.clone();
            continue;
        }
        if n.width != w {
            poly = false;
        }
        let a = n.args[0] as usize;
        let b = n.args[1] as usize;
        match n.op {
            MOp::Var(v) => {
                local[i] = true;
                deg[i] = 1;
                let mut d = zeros.clone();
                if let Some(x) = d.get_mut(v as usize) {
                    *x = 1;
                }
                if let Some(u) = used.get_mut(v as usize) {
                    *u = true;
                }
                vdeg[i] = d;
            }
            MOp::And | MOp::Or | MOp::Xor => {
                bitwise = true;
                for k in [a, b] {
                    if !local[k] {
                        poly = false;
                    }
                    if let Some(c) = &cst[k]
                        && !(c.is_zero() || c.is_ones())
                    {
                        uniform = false;
                    }
                }
                local[i] = true;
                deg[i] = 1;
                vdeg[i] = zeros.clone();
            }
            MOp::Not | MOp::Neg | MOp::Shl(_) => {
                local[i] = matches!(n.op, MOp::Not) && local[a];
                deg[i] = deg[a];
                vdeg[i] = vdeg[a].clone();
            }
            MOp::Add | MOp::Sub => {
                deg[i] = deg[a].max(deg[b]);
                vdeg[i] = vdeg[a]
                    .iter()
                    .zip(&vdeg[b])
                    .map(|(x, y)| *x.max(y))
                    .collect();
            }
            MOp::Mul => {
                deg[i] = deg[a].saturating_add(deg[b]).min(DEGREE_CAP);
                vdeg[i] = vdeg[a]
                    .iter()
                    .zip(&vdeg[b])
                    .map(|(x, y)| x.saturating_add(*y).min(DEGREE_CAP))
                    .collect();
            }
            MOp::LShr(_) | MOp::Zext | MOp::Sext | MOp::Trunc | MOp::Const(_) => {
                poly = false;
                vdeg[i] = zeros.clone();
            }
        }
    }
    for (v, &vw) in m.vars().iter().enumerate() {
        if used[v] && vw != w {
            poly = false;
        }
    }
    let root = nodes.len() - 1;
    Some(Profile {
        width: w,
        poly,
        uniform,
        bitwise,
        degree: deg[root],
        var_degree: std::mem::take(&mut vdeg[root]),
        used,
    })
}

// ----- sizes -----------------------------------------------------------------------------------

/// `C(n, k)`, saturating.
fn binom(n: u64, k: u64) -> u128 {
    if k > n {
        return 0;
    }
    let k = k.min(n - k);
    let mut r: u128 = 1;
    for i in 0..k {
        r = r.saturating_mul(u128::from(n - i)) / u128::from(i + 1);
        if r > u128::from(u64::MAX) {
            return u128::MAX;
        }
    }
    r
}

/// Points of the sparse test: `Σ_{k≤d} C(W,k)·(2^t − 1)^k`, saturating.
pub(crate) fn sparse_points(w: u16, t: usize, d: u32) -> u64 {
    let base: u128 = if t >= 64 { u128::MAX } else { (1u128 << t) - 1 };
    let mut total: u128 = 0;
    let mut pow: u128 = 1;
    for k in 0..=u64::from(d).min(u64::from(w)) {
        total = total.saturating_add(binom(u64::from(w), k).saturating_mul(pow));
        pow = pow.saturating_mul(base);
        if total >= u128::from(u64::MAX) {
            return u64::MAX;
        }
    }
    total as u64
}

/// The test chosen for two expressions, its points, and the variables it enumerates.
#[derive(Clone, Debug)]
struct Plan {
    cert: Cert,
    points: u64,
    /// The variables used by either side.
    used: Vec<usize>,
    /// Per used variable: the grid's radix (degree + 1).
    radix: Vec<u64>,
    degree: u32,
}

/// Every complete test that applies to `a` and `b` (same variables and width), in the order
/// ties are broken.
fn plans(a: &MbaExpr, pa: &Profile, pb: &Profile) -> Vec<Plan> {
    let used: Vec<usize> = (0..a.vars().len())
        .filter(|&v| pa.used.get(v) == Some(&true) || pb.used.get(v) == Some(&true))
        .collect();
    let t = used.len();
    let mut out = Vec::new();
    let degree = pa.degree.max(pb.degree);
    if pa.poly && pb.poly && pa.width == pb.width {
        if pa.uniform && pb.uniform && degree <= 1 && t <= SIGNATURE_VARS {
            out.push(Plan {
                cert: Cert::Signature,
                points: 1u64 << t,
                used: used.clone(),
                radix: Vec::new(),
                degree,
            });
        }
        if !pa.bitwise && !pb.bitwise {
            let radix: Vec<u64> = used
                .iter()
                .map(|&v| u64::from(pa.var_degree[v].max(pb.var_degree[v])) + 1)
                .collect();
            let points = radix
                .iter()
                .try_fold(1u64, |acc, &r| acc.checked_mul(r))
                .unwrap_or(u64::MAX);
            out.push(Plan {
                cert: Cert::Grid,
                points,
                used: used.clone(),
                radix,
                degree,
            });
        }
        out.push(Plan {
            cert: if degree <= 1 {
                Cert::SingleBit
            } else {
                Cert::Sparse
            },
            points: sparse_points(pa.width.bits(), t, degree),
            used: used.clone(),
            radix: Vec::new(),
            degree,
        });
    }
    let bits: u32 = used.iter().map(|&v| u32::from(a.vars()[v].bits())).sum();
    if bits <= EXHAUSTIVE_BITS {
        out.push(Plan {
            cert: Cert::Exhaustive,
            points: 1u64 << bits,
            used,
            radix: Vec::new(),
            degree,
        });
    }
    out
}

/// The cheapest complete test for `a` and `b` (same variables and width), if any applies.
fn plan(a: &MbaExpr, pa: &Profile, pb: &Profile) -> Option<Plan> {
    let mut best: Option<Plan> = None;
    for p in plans(a, pa, pb) {
        if best.as_ref().is_none_or(|b| p.points < b.points) {
            best = Some(p);
        }
    }
    best
}

/// Runs one kind of test on `a` and `b` if it applies (for tests: every test, not only the
/// cheapest). A forced sparse test uses degree at least 2. `Some(equal)`.
#[cfg(test)]
pub(crate) fn prove_with(a: &MbaExpr, b: &MbaExpr, cert: Cert) -> Option<bool> {
    let (pa, pb) = (profile(a)?, profile(b)?);
    let mut p = plans(a, &pa, &pb).into_iter().find(|p| {
        p.cert == cert
            || (cert == Cert::Sparse && p.cert == Cert::SingleBit)
            || (cert == Cert::SingleBit && p.cert == Cert::Sparse && p.degree <= 1)
    })?;
    if cert == Cert::Sparse && p.degree < 2 {
        p.degree = 2;
        p.cert = Cert::Sparse;
        p.points = sparse_points(pa.width.bits(), p.used.len(), 2);
    }
    let mut report = Report::new();
    match run(&mut Steps::new(u64::MAX), a, b, &p, &mut report).ok()? {
        Run::Equal => Some(true),
        Run::Differ(_) => Some(false),
        _ => None,
    }
}

// ----- point generators ------------------------------------------------------------------------

/// Enumerates the points of a plan, a block at a time.
struct Points {
    cert: Cert,
    /// Signature, exhaustive: the next point and the total.
    next: u64,
    total: u64,
    /// Grid: the counter and its radix.
    ctr: Vec<u64>,
    radix: Vec<u64>,
    /// Sparse: the width, the size of the current position set, the positions and their
    /// patterns (each a nonzero subset of the used variables).
    width: u16,
    t: usize,
    d: u32,
    k: usize,
    combo: Vec<u16>,
    pats: Vec<u64>,
    done: bool,
}

impl Points {
    fn new(plan: &Plan, width: u16) -> Points {
        Points {
            cert: plan.cert,
            next: 0,
            total: plan.points,
            ctr: vec![0; plan.radix.len()],
            radix: plan.radix.clone(),
            width,
            t: plan.used.len(),
            d: plan.degree,
            k: 0,
            combo: Vec::new(),
            pats: Vec::new(),
            done: plan.points == 0,
        }
    }

    /// Fills up to [`BLOCK`] points into `cols` (one column per variable of the expression;
    /// unused variables stay 0). Returns how many.
    fn fill<L: Lane>(
        &mut self,
        cols: &mut [Vec<L>],
        used: &[usize],
        vars: &[Width],
        masks: &[L::M],
    ) -> usize {
        for c in cols.iter_mut() {
            if c.len() != BLOCK {
                c.clear();
                c.resize(BLOCK, L::default());
            }
        }
        let mut n = 0;
        match self.cert {
            Cert::Signature => {
                while n < BLOCK && !self.done {
                    for (j, &v) in used.iter().enumerate() {
                        cols[v][n] = if self.next >> j & 1 == 1 {
                            L::not(L::default(), masks[v])
                        } else {
                            L::default()
                        };
                    }
                    self.next += 1;
                    self.done = self.next >= self.total;
                    n += 1;
                }
            }
            Cert::Exhaustive => {
                while n < BLOCK && !self.done {
                    let mut rest = self.next;
                    for &v in used {
                        let bits = vars[v].bits();
                        let x = rest & ((1u64 << bits) - 1);
                        rest >>= bits;
                        cols[v][n] = L::small(x, masks[v]);
                    }
                    self.next += 1;
                    self.done = self.next >= self.total;
                    n += 1;
                }
            }
            Cert::Grid => {
                while n < BLOCK && !self.done {
                    for (j, &v) in used.iter().enumerate() {
                        cols[v][n] = L::small(self.ctr[j], masks[v]);
                    }
                    self.done = true;
                    for j in 0..self.ctr.len() {
                        self.ctr[j] += 1;
                        if self.ctr[j] < self.radix[j] {
                            self.done = false;
                            break;
                        }
                        self.ctr[j] = 0;
                    }
                    n += 1;
                }
            }
            Cert::SingleBit | Cert::Sparse => {
                while n < BLOCK && !self.done {
                    for (j, &v) in used.iter().enumerate() {
                        let mut x = L::default();
                        for (s, &pos) in self.combo.iter().enumerate() {
                            if self.pats[s] >> j & 1 == 1 {
                                x = L::or(x, L::pow2(pos, masks[v]));
                            }
                        }
                        cols[v][n] = x;
                    }
                    self.advance_sparse();
                    n += 1;
                }
            }
            // No points: never planned.
            Cert::Symbolic | Cert::Carries => self.done = true,
        }
        n
    }

    fn advance_sparse(&mut self) {
        let top = if self.t >= 64 {
            u64::MAX
        } else {
            1u64 << self.t
        };
        for s in (0..self.k).rev() {
            self.pats[s] += 1;
            if self.pats[s] < top {
                return;
            }
            self.pats[s] = 1;
        }
        // The next set of positions of the same size.
        let (k, w) = (self.k, self.width);
        for s in (0..k).rev() {
            if usize::from(self.combo[s]) < usize::from(w) - k + s {
                self.combo[s] += 1;
                for u in s + 1..k {
                    self.combo[u] = self.combo[u - 1] + 1;
                }
                return;
            }
        }
        // One more position.
        self.k += 1;
        if self.k as u64 > u64::from(self.d) || self.k > usize::from(w) || self.t == 0 {
            self.done = true;
            return;
        }
        self.combo = (0..self.k as u16).collect();
        self.pats = vec![1; self.k];
    }
}

// ----- running a test --------------------------------------------------------------------------

/// The outcome of one test.
enum Run {
    Equal,
    /// A point (one value per variable) where the sides differ.
    Differ(Vec<BitVec>),
    /// Not run: over the budget.
    OverBudget,
    /// Not run: over [`MAX_POINTS`].
    TooBig,
}

fn run<M: Meter>(
    meter: &mut M,
    a: &MbaExpr,
    b: &MbaExpr,
    plan: &Plan,
    report: &mut Report,
) -> Result<Run, M::Err> {
    let (Some(pa), Some(pb)) = (Program::new(a, false), Program::new(b, false)) else {
        return Ok(Run::TooBig);
    };
    let kind = Kind::of(pa.widest().max(pb.widest()));
    let per = (pa.len() + pb.len()) as u64;
    let lane = match kind {
        Kind::N64 => 1,
        Kind::N128 => 2,
        Kind::Wide => 8,
    };
    if plan.points > MAX_POINTS || plan.points.saturating_mul(per).saturating_mul(lane) > MAX_EFFORT
    {
        return Ok(Run::TooBig);
    }
    if plan.points.saturating_mul(per) > meter.left() {
        report.over_budget = true;
        return Ok(Run::OverBudget);
    }
    let width = a.width().map_or(1, |w| w.bits());
    match kind {
        Kind::N64 => run_in::<u64, M>(meter, a, &pa, &pb, plan, width, report),
        Kind::N128 => run_in::<u128, M>(meter, a, &pa, &pb, plan, width, report),
        Kind::Wide => run_in::<Wide, M>(meter, a, &pa, &pb, plan, width, report),
    }
}

fn run_in<L: Lane, M: Meter>(
    meter: &mut M,
    a: &MbaExpr,
    pa: &Program,
    pb: &Program,
    plan: &Plan,
    width: u16,
    report: &mut Report,
) -> Result<Run, M::Err> {
    let vars = a.vars();
    let masks: Vec<L::M> = vars.iter().map(|&w| L::mask(w)).collect();
    let mut cols: Vec<Vec<L>> = vec![Vec::with_capacity(BLOCK); vars.len()];
    let (mut ra, mut rb): (Vec<Vec<L>>, Vec<Vec<L>>) = (Vec::new(), Vec::new());
    let mut points = Points::new(plan, width);
    let per = (pa.len() + pb.len()) as u64;
    loop {
        let n = points.fill(&mut cols, &plan.used, vars, &masks);
        if n == 0 {
            return Ok(Run::Equal);
        }
        meter.charge(per * n as u64)?;
        report.points += n as u64;
        pa.run(&mut ra, &cols, n);
        pb.run(&mut rb, &cols, n);
        let (x, y) = (&ra[pa.root()][..n], &rb[pb.root()][..n]);
        if let Some(p) = (0..n).find(|&p| x[p] != y[p]) {
            let point = vars
                .iter()
                .enumerate()
                .map(|(v, &w)| cols[v][p].to_bv(w))
                .collect();
            return Ok(Run::Differ(point));
        }
    }
}

// ----- the refutation sample -------------------------------------------------------------------

/// The distinct constants of `ms`, sorted, with their neighbours `c ± 1`, `−c` and `~c`: the
/// values a point function or a rare carry pattern is likely to single out.
fn constant_pool(ms: &[&MbaExpr]) -> Vec<BitVec> {
    let mut consts: Vec<BitVec> = ms
        .iter()
        .flat_map(|m| m.nodes().iter())
        .filter_map(|n| match n.op {
            MOp::Const(v) => Some(v),
            _ => None,
        })
        .collect();
    consts.sort();
    consts.dedup();
    let mut pool: Vec<BitVec> = Vec::new();
    for c in consts {
        let one = BitVec::one(c.width());
        for v in [
            c,
            BitVec::bin_unchecked(BinOp::Add, &c, &one),
            BitVec::bin_unchecked(BinOp::Sub, &c, &one),
            BitVec::un_unchecked(UnOp::Neg, &c),
            BitVec::un_unchecked(UnOp::Not, &c),
        ] {
            if !pool.contains(&v) {
                pool.push(v);
            }
        }
    }
    pool.truncate(32);
    pool
}

/// SplitMix64 words from `state`.
fn next_word(state: &mut u64) -> u64 {
    *state = state.wrapping_add(0x9e37_79b9_7f4a_7c15);
    let mut z = *state;
    z = (z ^ (z >> 30)).wrapping_mul(0xbf58_476d_1ce4_e5b9);
    z = (z ^ (z >> 27)).wrapping_mul(0x94d0_49bb_1331_11eb);
    z ^ (z >> 31)
}

/// The refutation sample for `ms` over variables `vars`: [`SAMPLE_POINTS`] points (point-major),
/// deterministic in `seed`. Zero, all-ones, one and the signed minimum for every variable; then
/// the constants of the expressions and their neighbours (each variable takes each of them at
/// some point); then points whose set bits lie at one position; then seeded random values.
/// A filter that catches wrong answers early; never evidence.
pub(crate) fn sample_points(vars: &[Width], ms: &[&MbaExpr], seed: u64) -> Vec<Vec<BitVec>> {
    let pool = constant_pool(ms);
    let fit = |c: &BitVec, w: Width| BitVec::wrapping_from_limbs(w, c.limbs());
    let mut pts: Vec<Vec<BitVec>> = Vec::with_capacity(SAMPLE_POINTS);
    for k in 0..4 {
        pts.push(
            vars.iter()
                .map(|&w| match k {
                    0 => BitVec::zero(w),
                    1 => BitVec::ones(w),
                    2 => BitVec::one(w),
                    _ => BitVec::smin(w),
                })
                .collect(),
        );
    }
    for q in 0..pool.len() {
        pts.push(
            vars.iter()
                .enumerate()
                .map(|(v, &w)| fit(&pool[(q + v) % pool.len()], w))
                .collect(),
        );
    }
    // Single positions: at point `s`, the variables in pattern `s % 3 + 1` (bit `v` for
    // variable `v`, repeating every two variables) have bit `j_s` set, the others are 0.
    for s in 0..8usize {
        let pattern = s % 3 + 1;
        pts.push(
            vars.iter()
                .enumerate()
                .map(|(v, &w)| {
                    let bits = w.bits();
                    let j = [
                        0,
                        1,
                        bits / 2,
                        bits - 1,
                        2,
                        bits / 4,
                        3 * bits / 4,
                        bits.saturating_sub(2),
                    ][s]
                        .min(bits - 1);
                    if pattern >> (v % 2) & 1 == 1 {
                        <Wide as Lane>::pow2(j, w).to_bv(w)
                    } else {
                        BitVec::zero(w)
                    }
                })
                .collect(),
        );
    }
    let mut state = seed;
    while pts.len() < SAMPLE_POINTS {
        pts.push(
            vars.iter()
                .map(|&w| {
                    let limbs: Vec<u64> = (0..8).map(|_| next_word(&mut state)).collect();
                    BitVec::wrapping_from_limbs(w, &limbs)
                })
                .collect(),
        );
    }
    pts.truncate(SAMPLE_POINTS);
    pts
}

/// The first sample point where `a` and `b` differ, if any. `None` when they agree (or cannot
/// be compared).
pub(crate) fn refute(a: &MbaExpr, b: &MbaExpr, points: &[Vec<BitVec>]) -> Option<Vec<BitVec>> {
    let (pa, pb) = (Program::new(a, false)?, Program::new(b, false)?);
    let (va, vb) = (pa.eval_points(points), pb.eval_points(points));
    (0..points.len().min(va.len()).min(vb.len()))
        .find(|&p| va[p] != vb[p])
        .map(|p| points[p].clone())
}

// ----- the certificate -------------------------------------------------------------------------

/// Decides `a == b` (on every input) if one of the tests applies within the budget: the
/// cheapest direct test, else over abstracted atoms, else with known bits read as arithmetic,
/// else case by case. `Refuted` only with a concrete input where they differ; `Unknown` when
/// no test applies, a test is over the budget, or only skeletons over abstracted atoms were
/// found to differ. Expressions over different variables or of different widths are not
/// compared (`Unknown`).
pub(crate) fn prove<M: Meter>(a: &MbaExpr, b: &MbaExpr, meter: &mut M) -> Result<Report, M::Err> {
    let mut report = prove_at(a, b, meter, 0, false)?;
    // A refutation comes with an input where the sides differ; one without would be a bug
    // (decided nothing).
    if report.verdict == Verdict::Refuted
        && report
            .counterexample
            .as_ref()
            .is_none_or(|p| a.eval(p).is_none() || a.eval(p) == b.eval(p))
    {
        debug_assert!(false, "a refutation without a counterexample");
        report.verdict = Verdict::Unknown;
        report.counterexample = None;
        report.internal += 1;
    }
    Ok(report)
}

/// [`prove`] within `depth` splits; `lowered`: known bits were already read as arithmetic.
fn prove_at<M: Meter>(
    a: &MbaExpr,
    b: &MbaExpr,
    meter: &mut M,
    depth: u32,
    lowered: bool,
) -> Result<Report, M::Err> {
    let mut report = Report::new();
    if a.vars() != b.vars() || a.width().is_none() || a.width() != b.width() {
        return Ok(report);
    }
    if a == b {
        report.verdict = Verdict::Proved;
        return Ok(report);
    }
    let (Some(pa), Some(pb)) = (profile(a), profile(b)) else {
        return Ok(report);
    };
    // Abstraction never makes a polynomial test smaller; only a non-polynomial side needs it.
    let mut compose = true;
    let poly = pa.poly && pb.poly;
    let direct = plan(a, &pa, &pb);
    // A polynomial pair no test fits (or can afford, below): maybe the same polynomial.
    if direct.is_none() && poly && symbolic(meter, a, b, &mut report)? {
        return Ok(report);
    }
    if let Some(p) = direct {
        match run(meter, a, b, &p, &mut report)? {
            Run::Equal => {
                report.verdict = Verdict::Proved;
                report.cert = Some(p.cert);
                return Ok(report);
            }
            Run::Differ(point) => {
                report.verdict = Verdict::Refuted;
                report.cert = Some(p.cert);
                report.counterexample = Some(point);
                return Ok(report);
            }
            Run::OverBudget | Run::TooBig => {
                compose = !poly;
                if poly && symbolic(meter, a, b, &mut report)? {
                    return Ok(report);
                }
            }
        }
    }
    if compose {
        Compose::new(a, b).prove(meter, &mut report)?;
    }
    // Arithmetic read bitwise without products, which the atoms left open: bit-serially,
    // exactly.
    if compose
        && report.verdict == Verdict::Unknown
        && !report.over_budget
        && carries(meter, a, b, &mut report)?
    {
        return Ok(report);
    }
    // Undecided for lack of budget: more budget may decide it directly; nothing more is spent.
    if report.verdict != Verdict::Unknown || report.over_budget {
        return Ok(report);
    }
    // The same question with known bits read as arithmetic (equal functions, so a verdict on
    // them is one on `a` and `b`, at the same points); it splits too.
    if !lowered && (lowerable(a) || lowerable(b)) {
        let units = (a.nodes().len() + b.nodes().len()) as u64 * LOWER_COST;
        if units > meter.left() {
            report.over_budget = true;
            return Ok(report);
        }
        meter.charge(units)?;
        let (la, lb) = (lower_known_bits(a), lower_known_bits(b));
        if la.is_some() || lb.is_some() {
            let la = la.unwrap_or_else(|| a.clone());
            let lb = lb.unwrap_or_else(|| b.clone());
            let sub = prove_at(&la, &lb, meter, depth, true)?;
            report.points += sub.points;
            report.over_budget |= sub.over_budget;
            report.internal += sub.internal;
            if sub.verdict != Verdict::Unknown {
                report.verdict = sub.verdict;
                report.cert = sub.cert;
                report.compositional = sub.compositional;
                report.split = sub.split;
                report.known_bits = true;
                report.counterexample = sub.counterexample;
            }
            return Ok(report);
        }
    }
    if depth < SPLIT_DEPTH {
        split(a, b, meter, depth, &mut report)?;
    }
    Ok(report)
}

/// Whether `m` has a bitwise operation with exactly one constant operand (see
/// [`lower_known_bits`]).
pub(crate) fn lowerable(m: &MbaExpr) -> bool {
    let nodes = m.nodes();
    let konst = |i: u32| {
        nodes
            .get(i as usize)
            .is_some_and(|n| matches!(n.op, MOp::Const(_)))
    };
    nodes.iter().any(|n| {
        matches!(n.op, MOp::And | MOp::Or | MOp::Xor) && konst(n.args[0]) != konst(n.args[1])
    })
}

/// `m` with every `x op k` (`op` bitwise, `k` a constant) read as arithmetic where the bits of
/// `x` that are known (by the transfer functions of [`Facts`](crate::Facts)) cover the bits `k`
/// is 1 at, or those it is 0 at. With `z` and `o` the known-zero and known-one bits of `x`:
///
/// - `k` inside the known bits: `x & k = k & o`, `x | k = x + (k & z)`,
///   `x ^ k = x + (k & z) − (k & o)`;
/// - `~k` inside them: `x & k = x − (~k & o)`, `x | k = k | o`,
///   `x ^ k = (~k & o) − (~k & z) − 1 − x` (that is, `~x ^ ~k`).
///
/// `None` when there is none.
pub(crate) fn lower_known_bits(m: &MbaExpr) -> Option<MbaExpr> {
    use crate::Facts;
    use crate::facts::known::{bv_and, bv_not, bv_or};
    let nodes = m.nodes();
    let cst = constants(nodes);
    let candidate = |n: &MNode| {
        matches!(n.op, MOp::And | MOp::Or | MOp::Xor)
            && cst[n.args[0] as usize].is_some() != cst[n.args[1] as usize].is_some()
    };
    if !nodes.iter().any(candidate) {
        return None;
    }
    let mut facts: Vec<Facts> = Vec::with_capacity(nodes.len());
    let mut out = MbaExpr::new(m.vars().to_vec());
    let mut map: Vec<u32> = Vec::with_capacity(nodes.len());
    let mut changed = false;
    for n in nodes {
        let fa = |k: usize| facts.get(n.args[k] as usize).copied();
        let f = match n.op {
            MOp::Const(v) => Some(Facts::constant(&v)),
            MOp::Var(_) => Some(Facts::top(n.width)),
            // `a + a` is `a << 1` (the shift knows the low bit).
            MOp::Add if n.args[0] == n.args[1] => {
                let one = Facts::constant(&BitVec::one(n.width));
                Facts::apply_bin(BinOp::Shl, &fa(0)?, &one).ok()
            }
            MOp::Add | MOp::Sub | MOp::Mul | MOp::And | MOp::Or | MOp::Xor => {
                let op = match n.op {
                    MOp::Add => BinOp::Add,
                    MOp::Sub => BinOp::Sub,
                    MOp::Mul => BinOp::Mul,
                    MOp::And => BinOp::And,
                    MOp::Or => BinOp::Or,
                    _ => BinOp::Xor,
                };
                Facts::apply_bin(op, &fa(0)?, &fa(1)?).ok()
            }
            MOp::Neg => Facts::apply_un(UnOp::Neg, &fa(0)?).ok(),
            MOp::Not => Facts::apply_un(UnOp::Not, &fa(0)?).ok(),
            MOp::Shl(k) | MOp::LShr(k) => {
                let op = if matches!(n.op, MOp::Shl(_)) {
                    BinOp::Shl
                } else {
                    BinOp::LShr
                };
                let amount = Facts::constant(&BitVec::wrapping_from_u64(n.width, u64::from(k)));
                Facts::apply_bin(op, &fa(0)?, &amount).ok()
            }
            MOp::Zext => fa(0)?.zext(n.width).ok(),
            MOp::Sext => fa(0)?.sext(n.width).ok(),
            MOp::Trunc => fa(0)?.extract(0, n.width).ok(),
        }?;
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&x| map[x as usize])
            .collect();
        // The rewrite: `c` alone, `x + c`, or `c − x`.
        let mut rewrite: Option<(Option<bool>, BitVec, u32)> = None;
        if candidate(n) {
            let (x, k) = match cst[n.args[0] as usize] {
                Some(k) => (1, k),
                None => (0, cst[n.args[1] as usize]?),
            };
            let kb = facts[n.args[x] as usize].known();
            let (z, o) = (kb.known_zero(), kb.known_one());
            let unknown = bv_not(&kb.known());
            let nk = bv_not(&k);
            let sub = |a: &BitVec, b: &BitVec| BitVec::bin_unchecked(BinOp::Sub, a, b);
            let one = BitVec::one(n.width);
            if bv_and(&k, &unknown).is_zero() {
                rewrite = Some(match n.op {
                    MOp::And => (None, bv_and(&k, &o), args[x]),
                    MOp::Or => (Some(true), bv_and(&k, &z), args[x]),
                    _ => (Some(true), sub(&bv_and(&k, &z), &bv_and(&k, &o)), args[x]),
                });
            } else if bv_and(&nk, &unknown).is_zero() {
                rewrite = Some(match n.op {
                    MOp::And => (
                        Some(true),
                        sub(&BitVec::zero(n.width), &bv_and(&nk, &o)),
                        args[x],
                    ),
                    MOp::Or => (None, bv_or(&k, &o), args[x]),
                    _ => (
                        Some(false),
                        sub(&sub(&bv_and(&nk, &o), &bv_and(&nk, &z)), &one),
                        args[x],
                    ),
                });
            }
        }
        let r = match rewrite {
            Some((form, c, x)) => {
                changed = true;
                let c = out.push(MOp::Const(c), &[]).ok()?;
                match form {
                    None => c,
                    Some(true) => out.push(MOp::Add, &[x, c]).ok()?,
                    Some(false) => out.push(MOp::Sub, &[c, x]).ok()?,
                }
            }
            None => match n.op {
                MOp::Zext | MOp::Sext | MOp::Trunc => out.push_cast(n.op, args[0], n.width).ok()?,
                op => out.push(op, &args).ok()?,
            },
        };
        facts.push(f);
        map.push(r);
    }
    changed.then_some(out)
}

/// A variable both sides read only as `v & M` (constant masks `M`, at most [`SPLIT_BITS`]
/// bits together), and those bits: the sides depend on nothing else of it.
fn narrow_var(a: &MbaExpr, b: &MbaExpr) -> Option<(u32, Vec<u32>)> {
    let nv = a.vars().len();
    let mut masks: Vec<Option<BitVec>> = vec![None; nv];
    let mut wide = vec![false; nv];
    for m in [a, b] {
        let nodes = m.nodes();
        let live = live(m);
        let cst = constants(nodes);
        if let Some(MOp::Var(v)) = m.root().map(|r| nodes[r as usize].op) {
            *wide.get_mut(v as usize)? = true;
        }
        for (i, n) in nodes.iter().enumerate() {
            if !live[i] {
                continue;
            }
            let args = &n.args[..n.op.arity()];
            for (k, &arg) in args.iter().enumerate() {
                let MOp::Var(v) = nodes[arg as usize].op else {
                    continue;
                };
                let mask = match n.op {
                    MOp::And => cst[args[1 - k] as usize],
                    _ => None,
                };
                let (Some(slot), Some(flag)) =
                    (masks.get_mut(v as usize), wide.get_mut(v as usize))
                else {
                    return None;
                };
                match mask {
                    Some(c) => {
                        *slot = Some(match slot {
                            Some(x) => BitVec::bin_unchecked(BinOp::Or, x, &c),
                            None => c,
                        })
                    }
                    None => *flag = true,
                }
            }
        }
    }
    (0..nv)
        .filter_map(|v| {
            let mask = masks[v].filter(|_| !wide[v])?;
            let bits: Vec<u32> = (0..mask.width().bits())
                .filter(|&j| mask.bit(j).unwrap_or(false))
                .map(u32::from)
                .collect();
            (bits.len() as u32 <= SPLIT_BITS).then_some((v as u32, bits))
        })
        .min_by_key(|(_, bits)| bits.len())
}

/// A variable whose low `j` bits (`1 ≤ j ≤` [`SPLIT_BITS`], `j` below its width) are all
/// that bitwise operations with constants read of arithmetic over it: `t op k` with `t` built
/// from variables and constants by `+ − · neg <<`, whose low `j` bits depend only on theirs, and
/// `k` all zeros or all ones above bit `j`. Once those bits are known, so are the bits `k`
/// reads (see [`lower_known_bits`]). The variable with the fewest, and that many.
fn low_var(a: &MbaExpr, b: &MbaExpr) -> Option<(u32, u32)> {
    use crate::facts::known::{bv_not, leading_zeros};
    let nv = a.vars().len();
    let mut need: Vec<u32> = vec![0; nv];
    for m in [a, b] {
        let nodes = m.nodes();
        let live = live(m);
        let cst = constants(nodes);
        // Per node: the variables it is arithmetic over (`None` when it reads one otherwise).
        let mut arith: Vec<Option<u64>> = Vec::with_capacity(nodes.len());
        for (i, n) in nodes.iter().enumerate() {
            let args = &n.args[..n.op.arity()];
            let vars = match n.op {
                _ if cst[i].is_some() => Some(0),
                MOp::Var(x) if x < 64 => Some(1u64 << x),
                MOp::Add | MOp::Sub | MOp::Mul | MOp::Neg | MOp::Shl(_) => args
                    .iter()
                    .try_fold(0u64, |acc, &x| Some(acc | arith[x as usize]?)),
                _ => None,
            };
            arith.push(vars);
        }
        for (i, n) in nodes.iter().enumerate() {
            if !live[i] || !matches!(n.op, MOp::And | MOp::Or | MOp::Xor) {
                continue;
            }
            let (x, k) = match (cst[n.args[0] as usize], cst[n.args[1] as usize]) {
                (None, Some(k)) => (n.args[0], k),
                (Some(k), None) => (n.args[1], k),
                _ => continue,
            };
            let bits = u32::from(k.width().bits());
            let len = |c: &BitVec| bits - leading_zeros(c);
            let j = len(&k).min(len(&bv_not(&k)));
            if j == 0 || j > SPLIT_BITS || j >= bits {
                continue;
            }
            let Some(mut set) = arith[x as usize] else {
                continue;
            };
            while set != 0 {
                let v = set.trailing_zeros() as usize;
                if let Some(nj) = need.get_mut(v) {
                    *nj = (*nj).max(j);
                }
                set &= set - 1;
            }
        }
    }
    (0..nv)
        .filter(|&v| need[v] > 0)
        .min_by_key(|&v| (need[v], v))
        .map(|v| (v as u32, need[v]))
}

/// How a split replaces its variable in one case.
#[derive(Copy, Clone, Debug)]
enum Case {
    /// By a constant.
    Value(BitVec),
    /// By `(v << j) + b`: onto the values whose low `j` bits are `b`, as `v` ranges over all.
    Low(u16, BitVec),
}

impl Case {
    /// The variable's value in this case where the specialized sides take `x`.
    fn value(&self, x: &BitVec) -> BitVec {
        match *self {
            Case::Value(c) => c,
            Case::Low(j, b) => BitVec::bin_unchecked(
                BinOp::Add,
                &crate::facts::known::bv_shl(x, u32::from(j)),
                &b,
            ),
        }
    }
}

/// The variable to split on and its cases: one both sides read only through masks of a few
/// bits (each assignment of those bits), else one whose low bits are what bitwise operations
/// with constants read ([`low_var`]; each value of them).
fn cases(a: &MbaExpr, b: &MbaExpr) -> Option<(u32, Vec<Case>)> {
    if let Some((v, bits)) = narrow_var(a, b) {
        let w = *a.vars().get(v as usize)?;
        let cases = (0..1u64 << bits.len())
            .map(|case| {
                let mut value = BitVec::zero(w);
                for (j, &pos) in bits.iter().enumerate() {
                    if case >> j & 1 == 1 {
                        let one = crate::facts::known::bv_shl(&BitVec::one(w), pos);
                        value = BitVec::bin_unchecked(BinOp::Or, &value, &one);
                    }
                }
                Case::Value(value)
            })
            .collect();
        return Some((v, cases));
    }
    let (v, j) = low_var(a, b)?;
    let w = *a.vars().get(v as usize)?;
    let cases = (0..1u64 << j)
        .map(|low| Case::Low(j as u16, BitVec::wrapping_from_u64(w, low)))
        .collect();
    Some((v, cases))
}

/// `m` with variable `v` replaced as `case` says (the variables unchanged).
fn specialize(m: &MbaExpr, v: u32, case: &Case) -> Option<MbaExpr> {
    let mut out = MbaExpr::new(m.vars().to_vec());
    let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
    for n in m.nodes() {
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&x| map.get(x as usize).copied())
            .collect::<Option<_>>()?;
        let r = match (n.op, case) {
            (MOp::Var(x), Case::Value(c)) if x == v => out.push(MOp::Const(*c), &[]),
            (MOp::Var(x), Case::Low(j, b)) if x == v => {
                let x = out.push(n.op, &[]).ok()?;
                let hi = out.push(MOp::Shl(*j), &[x]).ok()?;
                let lo = out.push(MOp::Const(*b), &[]).ok()?;
                out.push(MOp::Add, &[hi, lo])
            }
            (MOp::Zext | MOp::Sext | MOp::Trunc, _) => out.push_cast(n.op, args[0], n.width),
            (op, _) => out.push(op, &args),
        };
        map.push(r.ok()?);
    }
    Some(out)
}

/// [`split`] alone, at the top (for tests: the cases, whatever the direct tests would say).
#[cfg(test)]
pub(crate) fn by_cases(a: &MbaExpr, b: &MbaExpr) -> Report {
    let mut report = Report::new();
    let _ = split(a, b, &mut Steps::new(u64::MAX), 0, &mut report);
    report
}

/// Decides `a == b` case by case over a few bits of one variable ([`cases`]): when both read
/// it only through masks, each assignment of the masked bits is a case (the variable replaced
/// by that constant, which folds away); when bitwise operations with constants read only its
/// low bits, each value of those is a case (the variable replaced by `(v << j) + b`, which
/// makes those operations read known bits). Each case is proved on its own; the cases cover
/// every input. Proved when every case is; refuted by a case's counterexample (the variable
/// set to its value in that case). Declines (unknown) when a case is undecided or the cases
/// spend more than [`SPLIT_EFFORT`].
fn split<M: Meter>(
    a: &MbaExpr,
    b: &MbaExpr,
    meter: &mut M,
    depth: u32,
    report: &mut Report,
) -> Result<(), M::Err> {
    let Some((v, cases)) = cases(a, b) else {
        return Ok(());
    };
    let mut last = None;
    let mut spent = 0u64;
    for case in &cases {
        if spent > SPLIT_EFFORT {
            return Ok(());
        }
        let (Some(sa), Some(sb)) = (specialize(a, v, case), specialize(b, v, case)) else {
            return Ok(());
        };
        let before = meter.left();
        let sub = prove_at(&sa, &sb, meter, depth + 1, false)?;
        spent = spent.saturating_add(before.saturating_sub(meter.left()));
        report.points += sub.points;
        report.over_budget |= sub.over_budget;
        report.internal += sub.internal;
        report.compositional |= sub.compositional;
        report.known_bits |= sub.known_bits;
        match sub.verdict {
            Verdict::Proved => last = sub.cert.or(last),
            Verdict::Refuted => {
                let Some(mut point) = sub.counterexample else {
                    return Ok(());
                };
                if let Some(x) = point.get_mut(v as usize) {
                    *x = case.value(x);
                }
                report.verdict = Verdict::Refuted;
                report.cert = sub.cert;
                report.split = true;
                report.counterexample = Some(point);
                return Ok(());
            }
            Verdict::Unknown => return Ok(()),
        }
    }
    report.verdict = Verdict::Proved;
    report.cert = last;
    report.split = true;
    Ok(())
}

/// A skeleton comparison: its verdict, if a test ran, and for `Refuted` the input.
type Compared = (Option<Verdict>, Option<Vec<BitVec>>);

/// How a node takes part in a skeleton.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Role {
    /// Its value does not depend on any variable.
    Const,
    Var,
    /// `& | ^` (a bitwise function of its operands, which are read bitwise).
    Bitwise,
    /// `~`: bitwise under a bitwise reader, `−1 − a` otherwise.
    Not,
    /// `+ − · neg <<`: polynomial, but an atom when read by a bitwise operator.
    Arith,
    /// A right shift or a cast: always an atom.
    Opaque,
}

/// How a node is read.
#[derive(Copy, Clone, Debug, PartialEq, Eq, Hash)]
enum Ctx {
    Arith,
    Bitwise,
}

/// Which nodes a skeleton abstracts.
#[derive(Copy, Clone, Debug, PartialEq, Eq)]
enum Policy {
    /// Only where the fragment requires it (opaque nodes, arithmetic read bitwise).
    Minimal,
    /// The same atoms, read closer to their definitions: an atom whose class has a bitwise
    /// representative (a member that is a bitwise function of atoms of earlier classes and of
    /// variables, proved equal to it) is that function, and a bitwise function of atoms read
    /// arithmetically is its integer expansion `−a_∅ + Σ_T a_T·AND_T` (Möbius over its table,
    /// exact at every width) with each lone atom `AND_{a} = a` as its definition. Both are
    /// equal to the node at every input, so an identity of the skeletons for independent atoms
    /// is one of the expressions: `~a | ~b` read arithmetically is `−1 − (a & b)`, and
    /// `a | b` with `a = −(x ^ y)` is `−(x ^ y) + b − (a & b)`.
    Linear,
    /// Also every node below the root whose class is abstracted somewhere.
    Classes,
    /// Also the root, when its class is abstracted somewhere.
    Everything,
}

/// Both sides in one hash-consed DAG, with classes of nodes proved equal.
struct Compose {
    nodes: Vec<MNode>,
    cst: Vec<Option<BitVec>>,
    role: Vec<Role>,
    root_a: u32,
    root_b: u32,
    vars: Vec<Width>,
    /// Union-find parents.
    parent: Vec<u32>,
    /// Per class root: some member is abstracted (opaque, or arithmetic read bitwise).
    abstracted: Vec<bool>,
    /// Per class root: the variable among its members.
    var_member: Vec<Option<u32>>,
    /// Nodes abstracted wherever they are read, and operands of opaque nodes.
    forced: Vec<bool>,
    /// The two sides' nodes come first; the others are synthetic (complements of atoms,
    /// bitwise forms found at the sample), evaluated and paired like them but on neither side.
    sides: usize,
    intern: HashMap<MNode, u32>,
    /// Per class root: its bitwise representative, if any (see [`Policy::Linear`]).
    rep: Vec<Option<u32>>,
    /// The sample points and every node's values there, when those fit in 64 bits: each
    /// skeleton is checked against its side's values before a test decides on it.
    sample: Option<SampleValues>,
}

/// Sample points, and per node its values at them.
type SampleValues = (Vec<Vec<BitVec>>, Vec<Vec<u64>>);

/// The most distinct leaves of a bitwise function expanded by [`Policy::Linear`] (a table of
/// `2^k` entries), and of a bitwise form looked for at the sample.
const LINEAR_LEAVES: usize = 5;

fn commutative(op: &MOp) -> bool {
    matches!(op, MOp::Add | MOp::Mul | MOp::And | MOp::Or | MOp::Xor)
}

impl Compose {
    fn new(a: &MbaExpr, b: &MbaExpr) -> Compose {
        let mut nodes: Vec<MNode> = Vec::new();
        let mut intern: HashMap<MNode, u32> = HashMap::new();
        let mut roots = [0u32; 2];
        for (side, m) in [a, b].into_iter().enumerate() {
            let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
            for n in m.nodes() {
                let mut node = *n;
                for k in 0..n.op.arity() {
                    node.args[k] = map[n.args[k] as usize];
                }
                if commutative(&node.op) && node.args[0] > node.args[1] {
                    node.args.swap(0, 1);
                }
                let id = *intern.entry(node).or_insert_with(|| {
                    nodes.push(node);
                    nodes.len() as u32 - 1
                });
                map.push(id);
            }
            roots[side] = map.last().copied().unwrap_or(0);
        }
        let cst = constants(&nodes);
        let role: Vec<Role> = nodes
            .iter()
            .zip(&cst)
            .map(|(n, c)| Self::role_of(n, c.is_some()))
            .collect();
        let len = nodes.len();
        let var_member = nodes
            .iter()
            .enumerate()
            .map(|(i, n)| matches!(n.op, MOp::Var(_)).then_some(i as u32))
            .collect();
        let mut c = Compose {
            nodes,
            cst,
            role,
            root_a: roots[0],
            root_b: roots[1],
            vars: a.vars().to_vec(),
            parent: (0..len as u32).collect(),
            abstracted: vec![false; len],
            var_member,
            forced: vec![false; len],
            sides: len,
            intern,
            rep: Vec::new(),
            sample: None,
        };
        c.mark_forced();
        c.add_complements();
        c
    }

    fn role_of(node: &MNode, konst: bool) -> Role {
        match node.op {
            _ if konst => Role::Const,
            MOp::Var(_) => Role::Var,
            MOp::And | MOp::Or | MOp::Xor => Role::Bitwise,
            MOp::Not => Role::Not,
            MOp::Add | MOp::Sub | MOp::Mul | MOp::Neg | MOp::Shl(_) => Role::Arith,
            _ => Role::Opaque,
        }
    }

    /// A node over existing ones (hash-consed), on neither side.
    fn push_node(&mut self, mut node: MNode) -> u32 {
        if commutative(&node.op) && node.args[0] > node.args[1] {
            node.args.swap(0, 1);
        }
        if let Some(&i) = self.intern.get(&node) {
            return i;
        }
        let i = self.nodes.len() as u32;
        let k = node.op.arity();
        let a = if k > 0 {
            self.cst[node.args[0] as usize]
        } else {
            None
        };
        let b = if k > 1 {
            self.cst[node.args[1] as usize]
        } else {
            None
        };
        let c = if (k > 0 && a.is_none()) || (k > 1 && b.is_none()) {
            None
        } else {
            apply(&node, a.as_ref(), b.as_ref())
        };
        self.role.push(Self::role_of(&node, c.is_some()));
        self.nodes.push(node);
        self.cst.push(c);
        self.parent.push(i);
        self.abstracted.push(false);
        self.var_member.push(None);
        self.forced.push(false);
        self.intern.insert(node, i);
        i
    }

    /// `~a` for every atom `a`, so atoms that are complements of each other (`x − 1` and `−x`)
    /// meet at the sample, where they are paired and proved like any others.
    fn add_complements(&mut self) {
        for i in 0..self.sides {
            if self.forced[i] && matches!(self.role[i], Role::Arith | Role::Opaque) {
                let width = self.nodes[i].width;
                self.push_node(MNode {
                    op: MOp::Not,
                    width,
                    args: [i as u32, 0],
                });
            }
        }
    }

    /// Marks the nodes abstracted wherever they are read (opaque nodes, arithmetic read by a
    /// bitwise operator) and the operands of opaque nodes (definitions compared on their own).
    fn mark_forced(&mut self) {
        let mut seen: HashMap<(u32, Ctx), ()> = HashMap::new();
        let mut stack = vec![(self.root_a, Ctx::Arith), (self.root_b, Ctx::Arith)];
        while let Some((i, ctx)) = stack.pop() {
            if seen.insert((i, ctx), ()).is_some() {
                continue;
            }
            let n = self.nodes[i as usize];
            let args = &n.args[..n.op.arity()];
            match self.role[i as usize] {
                Role::Const | Role::Var => {}
                Role::Opaque => {
                    self.forced[i as usize] = true;
                    self.abstracted[i as usize] = true;
                    // The operand is compared as a definition of its own.
                    self.forced[args[0] as usize] = true;
                    stack.push((args[0], Ctx::Arith));
                }
                Role::Arith => {
                    if ctx == Ctx::Bitwise {
                        self.forced[i as usize] = true;
                        self.abstracted[i as usize] = true;
                    }
                    stack.extend(args.iter().map(|&k| (k, Ctx::Arith)));
                }
                Role::Bitwise => stack.extend(args.iter().map(|&k| (k, Ctx::Bitwise))),
                Role::Not => stack.push((args[0], ctx)),
            }
        }
    }

    fn find(&mut self, mut i: u32) -> u32 {
        while self.parent[i as usize] != i {
            let p = self.parent[i as usize];
            self.parent[i as usize] = self.parent[p as usize];
            i = p;
        }
        i
    }

    fn union(&mut self, a: u32, b: u32) {
        let (ra, rb) = (self.find(a), self.find(b));
        if ra == rb {
            return;
        }
        // The smaller index is the root, so a class is named by its first member.
        let (root, child) = if ra < rb { (ra, rb) } else { (rb, ra) };
        self.parent[child as usize] = root;
        self.abstracted[root as usize] |= self.abstracted[child as usize];
        if self.var_member[root as usize].is_none() {
            self.var_member[root as usize] = self.var_member[child as usize];
        }
    }

    /// Proves the two roots equal: evaluates every node at the refutation sample, pairs atoms
    /// (structure, congruence, proofs of their definitions), then compares the skeletons.
    fn prove<M: Meter>(&mut self, meter: &mut M, report: &mut Report) -> Result<(), M::Err> {
        report.compositional = true;
        // The sample, over the union of both sides.
        let mut all = MbaExpr::new(self.vars.clone());
        for n in &self.nodes {
            let r = match n.op {
                MOp::Zext | MOp::Sext | MOp::Trunc => all.push_cast(n.op, n.args[0], n.width),
                op => all.push(op, &n.args[..n.op.arity()]),
            };
            if r.is_err() {
                return Ok(());
            }
        }
        let Some(prog) = Program::new(&all, true) else {
            return Ok(());
        };
        let units = (prog.len() * SAMPLE_POINTS) as u64;
        if units > meter.left() {
            report.over_budget = true;
            return Ok(());
        }
        meter.charge(units)?;
        report.points += SAMPLE_POINTS as u64;
        let seed = crate::hash::combine(all.key()[0], all.key()[1]);
        let points = sample_points(&self.vars, &[&all], seed);
        let mut digests = digests(&prog, &points, self.nodes.len());
        let (ra, rb) = (self.root_a as usize, self.root_b as usize);
        if let Some(p) = (0..points.len()).find(|&p| digests[ra][p] != digests[rb][p]) {
            // A real input where the sides differ.
            report.verdict = Verdict::Refuted;
            report.counterexample = Some(points[p].clone());
            return Ok(());
        }
        let values = prog.widest() <= 64;
        if values {
            self.sample = Some((points.clone(), digests.clone()));
        }
        // Group nodes by width and sample values; pair within groups, operands first.
        let key = |i: usize| {
            let mut h = u64::from(self.nodes[i].width.bits());
            for &d in &digests[i] {
                h = crate::hash::combine(h, d);
            }
            h
        };
        let keys: Vec<u64> = (0..self.nodes.len()).map(key).collect();
        let wanted: std::collections::HashSet<u64> = (0..self.nodes.len())
            .filter(|&i| self.forced[i])
            .map(|i| keys[i])
            .collect();
        let mut groups: HashMap<u64, Vec<u32>> = HashMap::new();
        for i in 0..self.nodes.len() as u32 {
            let k = keys[i as usize];
            if self.role[i as usize] == Role::Const || !wanted.contains(&k) {
                continue;
            }
            let peers = groups.entry(k).or_default().clone();
            let mut tries = 0;
            for m in peers {
                if digests[m as usize] != digests[i as usize] {
                    continue;
                }
                if self.find(m) == self.find(i) {
                    break;
                }
                if tries >= PAIR_TRIES {
                    break;
                }
                tries += 1;
                if self.equal_defs(meter, report, i, m)? {
                    self.union(i, m);
                    break;
                }
            }
            groups.entry(k).or_default().push(i);
        }
        // Atoms that are bitwise functions of the leaves of their definitions, at 64 bits or
        // fewer (where a digest is the value).
        self.compute_reps();
        if values {
            self.bitwise_forms(meter, report, &mut digests)?;
            self.compute_reps();
            self.sample = Some((points.clone(), digests.clone()));
        }
        // Every class agrees at the sample (a pairing that does not is a bug: decline).
        for i in 0..self.nodes.len() as u32 {
            let r = self.find(i);
            if digests[r as usize] != digests[i as usize] {
                report.internal += 1;
                return Ok(());
            }
        }
        if self.find(self.root_a) == self.find(self.root_b) {
            report.verdict = Verdict::Proved;
            return Ok(());
        }
        for policy in [
            Policy::Minimal,
            Policy::Linear,
            Policy::Classes,
            Policy::Everything,
        ] {
            let (a, b) = (self.root_a, self.root_b);
            match self.compare(meter, report, a, b, policy)? {
                (Some(Verdict::Proved), _) => {
                    report.verdict = Verdict::Proved;
                    return Ok(());
                }
                (Some(Verdict::Refuted), point) => {
                    report.verdict = Verdict::Refuted;
                    report.counterexample = point;
                    return Ok(());
                }
                _ => {}
            }
        }
        Ok(())
    }

    /// Whether nodes `i` and `m` (of one width, agreeing at the sample) are proved equal: opaque
    /// nodes by congruence, others by comparing their definitions' skeletons.
    fn equal_defs<M: Meter>(
        &mut self,
        meter: &mut M,
        report: &mut Report,
        i: u32,
        m: u32,
    ) -> Result<bool, M::Err> {
        let (ni, nm) = (self.nodes[i as usize], self.nodes[m as usize]);
        let (oi, om) = (
            self.role[i as usize] == Role::Opaque,
            self.role[m as usize] == Role::Opaque,
        );
        if oi || om {
            return Ok(oi
                && om
                && ni.op == nm.op
                && ni.width == nm.width
                && self.find(ni.args[0]) == self.find(nm.args[0]));
        }
        for policy in [
            Policy::Minimal,
            Policy::Linear,
            Policy::Classes,
            Policy::Everything,
        ] {
            if self.compare(meter, report, i, m, policy)?.0 == Some(Verdict::Proved) {
                return Ok(true);
            }
        }
        Ok(false)
    }

    /// Compares the skeletons of nodes `x` and `y` under `policy` with a direct test. `Refuted`
    /// (with the input where they differ, in the original variables) only when no atom got a
    /// variable of its own: then the skeletons equal the expressions at every input.
    fn compare<M: Meter>(
        &mut self,
        meter: &mut M,
        report: &mut Report,
        x: u32,
        y: u32,
        policy: Policy,
    ) -> Result<Compared, M::Err> {
        let mut vm = VarMap::default();
        let (sx, sy) = if policy == Policy::Linear {
            (
                self.linear_skeleton(x, &mut vm),
                self.linear_skeleton(y, &mut vm),
            )
        } else {
            (
                self.skeleton(x, policy, &mut vm),
                self.skeleton(y, policy, &mut vm),
            )
        };
        let (Some(sx), Some(sy)) = (sx, sy) else {
            return Ok((None, None));
        };
        let w = self.nodes[x as usize].width;
        let (Some(a), Some(b)) = (vm.expr(&sx, w), vm.expr(&sy, w)) else {
            return Ok((None, None));
        };
        let (Some(pa), Some(pb)) = (profile(&a), profile(&b)) else {
            return Ok((None, None));
        };
        if !(pa.poly && pb.poly) {
            return Ok((None, None));
        }
        // A skeleton is its side's value wherever its variables take their nodes' values: at
        // the sample it must be. One that is not would be a bug; decline.
        if !self.agrees(&vm, [(&a, x), (&b, y)]) {
            report.internal += 1;
            return Ok((None, None));
        }
        let Some(p) = plan(&a, &pa, &pb) else {
            if symbolic(meter, &a, &b, report)? {
                return Ok((Some(Verdict::Proved), None));
            }
            if policy == Policy::Linear {
                return self.eliminate(meter, report, &mut vm, [a, b], w);
            }
            return Ok((None, None));
        };
        let direct = run(meter, &a, &b, &p, report)?;
        if matches!(direct, Run::TooBig | Run::OverBudget) && symbolic(meter, &a, &b, report)? {
            return Ok((Some(Verdict::Proved), None));
        }
        if policy == Policy::Linear
            && vm.abstracted
            && matches!(direct, Run::Differ(_) | Run::TooBig)
        {
            return self.eliminate(meter, report, &mut vm, [a, b], w);
        }
        Ok(match direct {
            Run::Equal => {
                report.cert = Some(p.cert);
                (Some(Verdict::Proved), None)
            }
            Run::Differ(point) if !vm.abstracted => {
                // Back to the original variables (the others stay 0).
                let mut orig: Vec<BitVec> = self.vars.iter().map(|&w| BitVec::zero(w)).collect();
                for (k, &(slot, _)) in vm.slots.iter().enumerate() {
                    if let Slot::Orig(v) = slot {
                        orig[v as usize] = point[k];
                    }
                }
                (Some(Verdict::Refuted), Some(orig))
            }
            Run::Differ(_) => (Some(Verdict::Unknown), None),
            Run::OverBudget | Run::TooBig => (None, None),
        })
    }

    /// Whether the skeletons agree with their nodes at the sample (when its values are kept):
    /// each variable of `vm` takes its node's or class's value at each point. A value the
    /// sample did not keep (a node the evaluation left out) checks nothing.
    fn agrees(&mut self, vm: &VarMap, sides: [(&MbaExpr, u32); 2]) -> bool {
        let Some((points, digests)) = self.sample.take() else {
            return true;
        };
        let class_root: Vec<u32> = vm
            .slots
            .iter()
            .map(|&(slot, _)| match slot {
                Slot::Class(c) => self.find(c),
                Slot::Orig(_) => 0,
            })
            .collect();
        let mut ok = true;
        'points: for (p, point) in points.iter().enumerate() {
            let inputs: Option<Vec<BitVec>> = vm
                .slots
                .iter()
                .zip(&class_root)
                .map(|(&(slot, sw), &c)| match slot {
                    Slot::Orig(v) => point.get(v as usize).copied(),
                    Slot::Class(_) => digests
                        .get(c as usize)
                        .and_then(|d| d.get(p))
                        .map(|&v| BitVec::wrapping_from_u64(sw, v)),
                })
                .collect();
            let Some(inputs) = inputs else {
                break;
            };
            for (skel, node) in sides {
                let w = self.nodes[node as usize].width;
                let Some(want) = digests
                    .get(node as usize)
                    .and_then(|d| d.get(p))
                    .map(|&v| BitVec::wrapping_from_u64(w, v))
                else {
                    continue;
                };
                if skel.eval(&inputs) != Some(want) {
                    ok = false;
                    break 'points;
                }
            }
        }
        self.sample = Some((points, digests));
        ok
    }

    /// Under [`Policy::Linear`], when the skeletons differ over independent atoms: an atom
    /// that a side reads only as `γ·v` in all (its class variable `v`: the side is its value
    /// at `v = 0` plus `γ·v` for every value of every variable, proved by a direct test, `γ`
    /// read at one point) stands for `γ` times its definition there, exactly. So `9·(a & −2) +
    /// 8·(a & 1) − 7·a − …` with `a = (x ^ y) + 1`, whose parts of `a` add up to `a`, meets a
    /// form in `x` and `y` alone. Then the sides are compared directly.
    fn eliminate<M: Meter>(
        &mut self,
        meter: &mut M,
        report: &mut Report,
        vm: &mut VarMap,
        sides: [MbaExpr; 2],
        w: Width,
    ) -> Result<Compared, M::Err> {
        // The definitions of the atoms with class variables (arithmetic ones), skeletons first,
        // so every expression has the final variables.
        let mut defs: Vec<(u32, Vec<SkelNode>)> = Vec::new();
        let mut k = 0;
        while k < vm.slots.len() && defs.len() < 4 {
            if let Slot::Class(c) = vm.slots[k].0
                && let Some(i) = (0..self.nodes.len() as u32)
                    .find(|&i| self.role[i as usize] == Role::Arith && self.find(i) == c)
                && let Some(d) = self.linear_skeleton(i, vm)
            {
                defs.push((k as u32, d));
            }
            k += 1;
        }
        let [a0, b0] = sides;
        // The sides again over every variable.
        let widen = |m: &MbaExpr, n: usize| -> Option<MbaExpr> {
            let mut out = MbaExpr::new(vec![w; n]);
            for node in m.nodes() {
                out.push(node.op, &node.args[..node.op.arity()]).ok()?;
            }
            Some(out)
        };
        let n = vm.slots.len();
        if vm.slots.iter().any(|&(_, sw)| sw != w) {
            return Ok((None, None));
        }
        let (Some(mut a), Some(mut b)) = (widen(&a0, n), widen(&b0, n)) else {
            return Ok((None, None));
        };
        let defs: Vec<(u32, MbaExpr)> = defs
            .iter()
            .filter_map(|(k, d)| Some((*k, vm.expr(d, w)?)))
            .collect();
        let zero = {
            let mut z = MbaExpr::new(vec![w; n]);
            z.push(MOp::Const(BitVec::zero(w)), &[]).ok();
            z
        };
        let mut changed = false;
        for (k, d) in &defs {
            for side in [&mut a, &mut b] {
                if !side.nodes().iter().any(|m| m.op == MOp::Var(*k)) {
                    continue;
                }
                let Some(s0) = substitute_var(side, *k, &zero) else {
                    continue;
                };
                // γ, read at the point where only `v` is 1.
                let mut at = vec![BitVec::zero(w); n];
                let (Some(v0), Some(v1)) = (side.eval(&at), {
                    at[*k as usize] = BitVec::one(w);
                    side.eval(&at)
                }) else {
                    continue;
                };
                let gamma = BitVec::bin_unchecked(BinOp::Sub, &v1, &v0);
                // t = s0 + γ·v.
                let mut t = s0.clone();
                let r0 = t.nodes().len() as u32 - 1;
                let (Ok(v), Ok(g)) = (t.push(MOp::Var(*k), &[]), t.push(MOp::Const(gamma), &[]))
                else {
                    continue;
                };
                let (Ok(m), true) = (t.push(MOp::Mul, &[v, g]), true) else {
                    continue;
                };
                if t.push(MOp::Add, &[r0, m]).is_err() {
                    continue;
                }
                let (Some(ps), Some(pt)) = (profile(side), profile(&t)) else {
                    continue;
                };
                if !(ps.poly && pt.poly) {
                    continue;
                }
                let linear = match plan(side, &ps, &pt) {
                    Some(p) => match run(meter, side, &t, &p, report)? {
                        Run::Equal => true,
                        Run::Differ(_) => false,
                        Run::TooBig | Run::OverBudget => symbolic(meter, side, &t, report)?,
                    },
                    None => symbolic(meter, side, &t, report)?,
                };
                if !linear {
                    continue;
                }
                if let Some(e) = substitute_var(&t, *k, d) {
                    *side = e;
                    changed = true;
                }
            }
        }
        if !changed {
            return Ok((None, None));
        }
        let (Some(pa), Some(pb)) = (profile(&a), profile(&b)) else {
            return Ok((None, None));
        };
        if !(pa.poly && pb.poly) {
            return Ok((None, None));
        }
        let Some(p) = plan(&a, &pa, &pb) else {
            return Ok(if symbolic(meter, &a, &b, report)? {
                (Some(Verdict::Proved), None)
            } else {
                (None, None)
            });
        };
        Ok(match run(meter, &a, &b, &p, report)? {
            Run::Equal => {
                report.cert = Some(p.cert);
                (Some(Verdict::Proved), None)
            }
            Run::Differ(_) => (Some(Verdict::Unknown), None),
            Run::OverBudget | Run::TooBig => {
                if symbolic(meter, &a, &b, report)? {
                    (Some(Verdict::Proved), None)
                } else {
                    (None, None)
                }
            }
        })
    }

    /// The nodes a bitwise function rooted at `k` reads (walking `& | ^ ~`): variables,
    /// constants and atoms.
    fn bitwise_leaves(&self, k: u32) -> Vec<u32> {
        let mut out = Vec::new();
        let mut seen: HashMap<u32, ()> = HashMap::new();
        let mut stack = vec![k];
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() {
                continue;
            }
            let n = self.nodes[i as usize];
            match self.role[i as usize] {
                Role::Bitwise | Role::Not => stack.extend(n.args[..n.op.arity()].iter().copied()),
                _ => out.push(i),
            }
        }
        out
    }

    /// Per class of atoms: a member that is a bitwise function (`& | ^ ~`) of variables,
    /// constants and atoms of classes named by earlier nodes, if one is, as its representative.
    /// Classes only refer to earlier ones, so reading atoms through representatives ends.
    fn compute_reps(&mut self) {
        self.rep = vec![None; self.nodes.len()];
        for k in 0..self.nodes.len() as u32 {
            if !matches!(self.role[k as usize], Role::Bitwise | Role::Not) {
                continue;
            }
            let c = self.find(k);
            if !self.abstracted[c as usize] || self.rep[c as usize].is_some() {
                continue;
            }
            let leaves = self.bitwise_leaves(k);
            let earlier = leaves.iter().all(|&l| match self.role[l as usize] {
                Role::Const | Role::Var => true,
                _ => self.find(l) < c,
            });
            if earlier {
                self.rep[c as usize] = Some(k);
            }
        }
    }

    /// The representative of atom `i`'s class, if it has one other than `i`.
    fn rep_of(&mut self, i: u32) -> Option<u32> {
        let c = self.find(i);
        self.rep
            .get(c as usize)
            .copied()
            .flatten()
            .filter(|&r| r != i)
    }

    /// The variables and atoms (by node) the definition of arithmetic node `y` reads, each
    /// class once: at most [`LINEAR_LEAVES`], else `None`.
    fn def_leaves(&mut self, y: u32) -> Option<Vec<u32>> {
        let mut out: Vec<u32> = Vec::new();
        let mut classes: Vec<u32> = Vec::new();
        let mut seen: HashMap<(u32, Ctx), ()> = HashMap::new();
        let n = self.nodes[y as usize];
        let mut stack: Vec<(u32, Ctx)> = n.args[..n.op.arity()]
            .iter()
            .map(|&k| (k, Ctx::Arith))
            .collect();
        while let Some((i, ctx)) = stack.pop() {
            if seen.insert((i, ctx), ()).is_some() {
                continue;
            }
            let n = self.nodes[i as usize];
            let leaf = match self.role[i as usize] {
                Role::Const => continue,
                Role::Var | Role::Opaque => true,
                Role::Arith => ctx == Ctx::Bitwise,
                Role::Bitwise | Role::Not => false,
            };
            if leaf {
                let c = self.find(i);
                if !classes.contains(&c) {
                    if out.len() == LINEAR_LEAVES {
                        return None;
                    }
                    classes.push(c);
                    out.push(i);
                }
                continue;
            }
            let sub = match self.role[i as usize] {
                Role::Bitwise => Ctx::Bitwise,
                Role::Not => ctx,
                _ => Ctx::Arith,
            };
            stack.extend(n.args[..n.op.arity()].iter().map(|&k| (k, sub)));
        }
        // And the variables the atoms among them are defined over, while there is room: a
        // subterm can be a bitwise function of an atom and the variables inside it together
        // (`−(a & x)` with `a = −(x & y)` is `(a & ~x) | (x & y)`).
        let mut stack: Vec<u32> = out
            .iter()
            .copied()
            .filter(|&l| self.role[l as usize] == Role::Arith)
            .collect();
        let mut seen: HashMap<u32, ()> = HashMap::new();
        while let Some(i) = stack.pop() {
            if seen.insert(i, ()).is_some() {
                continue;
            }
            let n = self.nodes[i as usize];
            if self.role[i as usize] == Role::Var {
                let c = self.find(i);
                if !classes.contains(&c) && out.len() < LINEAR_LEAVES {
                    classes.push(c);
                    out.push(i);
                }
                continue;
            }
            stack.extend(n.args[..n.op.arity()].iter().copied());
        }
        Some(out)
    }

    /// Bitwise forms: for each atom (arithmetic read bitwise) whose bits at every sample point
    /// are one function of the bits of the leaves of its definition, that function as nodes
    /// (its algebraic normal form), paired with the atom once proved equal (`(e − 1 & d) − e`
    /// is `~(e − 1) | d`). `digests` are values here (64 bits or fewer), and grow with the
    /// nodes.
    fn bitwise_forms<M: Meter>(
        &mut self,
        meter: &mut M,
        report: &mut Report,
        digests: &mut Vec<Vec<u64>>,
    ) -> Result<(), M::Err> {
        let atoms: Vec<u32> = (0..self.sides as u32)
            .filter(|&i| self.forced[i as usize] && self.role[i as usize] == Role::Arith)
            .collect();
        for y in atoms {
            if self.rep_of(y).is_some() || self.find(y) != y {
                continue;
            }
            let Some(leaves) = self.def_leaves(y) else {
                continue;
            };
            if leaves.is_empty() {
                continue;
            }
            let w = self.nodes[y as usize].width;
            let points = digests[y as usize].len();
            let units = (points * leaves.len()) as u64;
            if units > meter.left() {
                report.over_budget = true;
                return Ok(());
            }
            meter.charge(units)?;
            let (mut seen, mut ones) = (0u64, 0u64);
            let mut fits = true;
            'points: for (p, &v) in digests[y as usize].iter().enumerate().take(points) {
                for j in 0..u32::from(w.bits()) {
                    let e = leaves.iter().enumerate().fold(0u32, |e, (t, &l)| {
                        e | (((digests[l as usize][p] >> j) & 1) as u32) << t
                    });
                    let bit = (v >> j) & 1;
                    if seen >> e & 1 == 1 {
                        if ones >> e & 1 != bit {
                            fits = false;
                            break 'points;
                        }
                    } else {
                        seen |= 1 << e;
                        ones |= bit << e;
                    }
                }
            }
            if !fits {
                continue;
            }
            let root = self.anf_nodes(ones, &leaves, w);
            self.extend_digests(digests);
            if digests[root as usize] != digests[y as usize] || self.find(root) == self.find(y) {
                continue;
            }
            if self.equal_defs(meter, report, y, root)? {
                self.union(y, root);
            }
        }
        Ok(())
    }

    /// The function with table `t` over `leaves` (entry `e` for leaf `j` at bit `j` of `e`) as
    /// nodes: the xor of the conjunctions of its algebraic normal form.
    fn anf_nodes(&mut self, t: u64, leaves: &[u32], w: Width) -> u32 {
        let k = leaves.len();
        let mut a: Vec<bool> = (0..1usize << k).map(|e| t >> e & 1 == 1).collect();
        for b in 0..k {
            for e in 0..1usize << k {
                if e >> b & 1 == 1 {
                    a[e] ^= a[e ^ 1 << b];
                }
            }
        }
        let mut acc: Option<u32> = None;
        for (e, &on) in a.iter().enumerate().skip(1) {
            if !on {
                continue;
            }
            let mut c: Option<u32> = None;
            for (j, &l) in leaves.iter().enumerate() {
                if e >> j & 1 == 1 {
                    c = Some(match c {
                        None => l,
                        Some(x) => self.push_node(MNode {
                            op: MOp::And,
                            width: w,
                            args: [x, l],
                        }),
                    });
                }
            }
            if let Some(c) = c {
                acc = Some(match acc {
                    None => c,
                    Some(x) => self.push_node(MNode {
                        op: MOp::Xor,
                        width: w,
                        args: [x, c],
                    }),
                });
            }
        }
        let zero = self.push_node(MNode {
            op: MOp::Const(BitVec::zero(w)),
            width: w,
            args: [0, 0],
        });
        let x = acc.unwrap_or(zero);
        if a[0] {
            self.push_node(MNode {
                op: MOp::Not,
                width: w,
                args: [x, 0],
            })
        } else {
            x
        }
    }

    /// Digests (values, at 64 bits or fewer) of the nodes added since they were computed: only
    /// constants and `& | ^ ~` are added.
    fn extend_digests(&self, digests: &mut Vec<Vec<u64>>) {
        let points = digests.first().map_or(0, Vec::len);
        for i in digests.len()..self.nodes.len() {
            let n = self.nodes[i];
            let bits = n.width.bits();
            let mask = if bits >= 64 {
                u64::MAX
            } else {
                (1u64 << bits) - 1
            };
            let col = |k: u32, p: usize| digests[k as usize].get(p).copied().unwrap_or(0);
            let v: Vec<u64> = (0..points)
                .map(|p| match n.op {
                    MOp::Const(c) => c.limbs().first().copied().unwrap_or(0) & mask,
                    MOp::And => col(n.args[0], p) & col(n.args[1], p),
                    MOp::Or => col(n.args[0], p) | col(n.args[1], p),
                    MOp::Xor => col(n.args[0], p) ^ col(n.args[1], p),
                    MOp::Not => !col(n.args[0], p) & mask,
                    _ => 0,
                })
                .collect();
            digests.push(v);
        }
    }

    /// The integer expansion of the bitwise function at `i` (read arithmetically) over its
    /// leaves, when it reads an atom (see [`Policy::Linear`]): atoms are read through their
    /// representatives, and only 0 and all-ones constants are allowed.
    fn expansion(&mut self, i: u32) -> Option<Expansion> {
        let w = self.nodes[i as usize].width;
        // The leaves, by class, and the internal nodes in post-order.
        let mut leaves: Vec<(u32, u32)> = Vec::new();
        let mut post: Vec<u32> = Vec::new();
        let mut state: HashMap<u32, bool> = HashMap::new();
        let mut stack: Vec<(u32, bool)> = vec![(i, false)];
        let mut atom = false;
        while let Some((k, done)) = stack.pop() {
            if done {
                post.push(k);
                continue;
            }
            if state.contains_key(&k) {
                continue;
            }
            state.insert(k, true);
            let n = self.nodes[k as usize];
            match self.role[k as usize] {
                Role::Const => {
                    let c = self.cst[k as usize]?;
                    if !(c.is_zero() || c.is_ones()) {
                        return None;
                    }
                    post.push(k);
                }
                Role::Bitwise | Role::Not => {
                    stack.push((k, true));
                    stack.extend(n.args[..n.op.arity()].iter().map(|&a| (a, false)));
                }
                Role::Var | Role::Arith | Role::Opaque => {
                    if self.role[k as usize] != Role::Var
                        && let Some(r) = self.rep_of(k)
                    {
                        // Read through its representative.
                        stack.push((k, true));
                        stack.push((r, false));
                        continue;
                    }
                    atom |= self.role[k as usize] != Role::Var;
                    let c = self.find(k);
                    if !leaves.iter().any(|&(_, lc)| lc == c) {
                        if leaves.len() == LINEAR_LEAVES {
                            return None;
                        }
                        leaves.push((k, c));
                    }
                    post.push(k);
                }
            }
        }
        if !atom {
            return None;
        }
        let k = leaves.len();
        let full: u64 = if k == 6 {
            u64::MAX
        } else {
            (1u64 << (1u32 << k)) - 1
        };
        let column = |j: usize| {
            (0..1u64 << k)
                .filter(|e| e >> j & 1 == 1)
                .fold(0u64, |t, e| t | 1 << e)
        };
        let mut table: HashMap<u32, u64> = HashMap::new();
        for &n in &post {
            let node = self.nodes[n as usize];
            let v = match self.role[n as usize] {
                Role::Const => {
                    if self.cst[n as usize]?.is_zero() {
                        0
                    } else {
                        full
                    }
                }
                Role::Var | Role::Arith | Role::Opaque => match self.rep_of(n) {
                    Some(r) if self.role[n as usize] != Role::Var => *table.get(&r)?,
                    _ => {
                        let c = self.find(n);
                        column(leaves.iter().position(|&(_, lc)| lc == c)?)
                    }
                },
                Role::Not => !*table.get(&node.args[0])? & full,
                Role::Bitwise => {
                    let (a, b) = (*table.get(&node.args[0])?, *table.get(&node.args[1])?);
                    match node.op {
                        MOp::And => a & b,
                        MOp::Or => a | b,
                        _ => a ^ b,
                    }
                }
            };
            table.insert(n, v);
        }
        let t = *table.get(&i)?;
        // Möbius: a_T = Σ_{U⊆T} (−1)^{|T|−|U|}·f(U).
        let mut a: Vec<i64> = (0..1usize << k).map(|e| (t >> e & 1) as i64).collect();
        for b in 0..k {
            for e in 0..1usize << k {
                if e >> b & 1 == 1 {
                    a[e] -= a[e ^ 1 << b];
                }
            }
        }
        let konst = BitVec::wrapping_from_i128(w, -i128::from(a[0]));
        let mut terms = Vec::new();
        for (e, &c) in a.iter().enumerate().skip(1) {
            if c == 0 {
                continue;
            }
            let members: Vec<u32> = (0..k)
                .filter(|&j| e >> j & 1 == 1)
                .map(|j| leaves[j].0)
                .collect();
            let reads: Vec<(u32, Ctx)> = if let [l] = members.as_slice() {
                // A lone atom is its definition; an opaque one stays an atom.
                let ctx = if self.role[*l as usize] == Role::Arith {
                    Ctx::Arith
                } else {
                    Ctx::Bitwise
                };
                vec![(*l, ctx)]
            } else {
                members.iter().map(|&l| (l, Ctx::Bitwise)).collect()
            };
            terms.push((BitVec::wrapping_from_i128(w, i128::from(c)), reads));
        }
        Some(Expansion {
            width: w,
            konst,
            terms,
        })
    }

    /// The skeleton of node `root` under [`Policy::Linear`].
    fn linear_skeleton(&mut self, root: u32, vm: &mut VarMap) -> Option<Vec<SkelNode>> {
        enum Item {
            Visit(u32, Ctx),
            Finish(u32, Ctx),
            Alias(u32, u32),
            Expand(u32, usize),
        }
        let mut out: Vec<SkelNode> = Vec::new();
        let mut memo: HashMap<(u32, Ctx), u32> = HashMap::new();
        let mut plans: Vec<Expansion> = Vec::new();
        let mut stack = vec![Item::Visit(root, Ctx::Arith)];
        while let Some(item) = stack.pop() {
            match item {
                Item::Visit(i, ctx) => {
                    if memo.contains_key(&(i, ctx)) {
                        continue;
                    }
                    let n = self.nodes[i as usize];
                    if let Some(c) = self.cst[i as usize] {
                        out.push(SkelNode::Const(c));
                        memo.insert((i, ctx), out.len() as u32 - 1);
                        continue;
                    }
                    if let MOp::Var(x) = n.op {
                        out.push(SkelNode::Var(vm.orig(x, n.width)));
                        memo.insert((i, ctx), out.len() as u32 - 1);
                        continue;
                    }
                    let role = self.role[i as usize];
                    if role == Role::Opaque || (role == Role::Arith && ctx == Ctx::Bitwise) {
                        if ctx == Ctx::Bitwise
                            && let Some(r) = self.rep_of(i)
                        {
                            stack.push(Item::Alias(i, r));
                            stack.push(Item::Visit(r, Ctx::Bitwise));
                            continue;
                        }
                        let c = self.find(i);
                        let v = match self.var_member[c as usize] {
                            Some(vi) => match self.nodes[vi as usize].op {
                                MOp::Var(x) => vm.orig(x, n.width),
                                _ => return None,
                            },
                            None => vm.class(c, n.width),
                        };
                        out.push(SkelNode::Var(v));
                        memo.insert((i, ctx), out.len() as u32 - 1);
                        continue;
                    }
                    if role == Role::Bitwise
                        && ctx == Ctx::Arith
                        && let Some(e) = self.expansion(i)
                    {
                        stack.push(Item::Expand(i, plans.len()));
                        for (_, reads) in &e.terms {
                            stack.extend(reads.iter().map(|&(l, c)| Item::Visit(l, c)));
                        }
                        plans.push(e);
                        continue;
                    }
                    let sub = match role {
                        Role::Bitwise => Ctx::Bitwise,
                        Role::Not => ctx,
                        _ => Ctx::Arith,
                    };
                    stack.push(Item::Finish(i, ctx));
                    stack.extend(n.args[..n.op.arity()].iter().map(|&k| Item::Visit(k, sub)));
                }
                Item::Finish(i, ctx) => {
                    let n = self.nodes[i as usize];
                    let sub = match self.role[i as usize] {
                        Role::Bitwise => Ctx::Bitwise,
                        Role::Not => ctx,
                        _ => Ctx::Arith,
                    };
                    let mut args = [0u32; 2];
                    for (k, &a) in n.args[..n.op.arity()].iter().enumerate() {
                        args[k] = *memo.get(&(a, sub))?;
                    }
                    out.push(SkelNode::Op(n.op, args));
                    memo.insert((i, ctx), out.len() as u32 - 1);
                }
                Item::Alias(i, r) => {
                    let v = *memo.get(&(r, Ctx::Bitwise))?;
                    memo.insert((i, Ctx::Bitwise), v);
                }
                Item::Expand(i, e) => {
                    let plan = &plans[e];
                    let mut acc: Option<u32> = None;
                    for (c, reads) in &plan.terms {
                        let mut t = *memo.get(&reads[0])?;
                        for r in &reads[1..] {
                            let x = *memo.get(r)?;
                            out.push(SkelNode::Op(MOp::And, [t, x]));
                            t = out.len() as u32 - 1;
                        }
                        if *c != BitVec::one(plan.width) {
                            out.push(SkelNode::Const(*c));
                            out.push(SkelNode::Op(MOp::Mul, [t, out.len() as u32 - 1]));
                            t = out.len() as u32 - 1;
                        }
                        acc = Some(match acc {
                            None => t,
                            Some(a) => {
                                out.push(SkelNode::Op(MOp::Add, [a, t]));
                                out.len() as u32 - 1
                            }
                        });
                    }
                    // The expansion's own node: a lone term with coefficient 1 and no
                    // constant is its leaf's node, pushed long before (not the last one).
                    let result = match acc {
                        Some(a) if plan.konst.is_zero() => a,
                        _ => {
                            out.push(SkelNode::Const(plan.konst));
                            let k = out.len() as u32 - 1;
                            match acc {
                                Some(a) => {
                                    out.push(SkelNode::Op(MOp::Add, [a, k]));
                                    out.len() as u32 - 1
                                }
                                None => k,
                            }
                        }
                    };
                    memo.insert((i, Ctx::Arith), result);
                }
            }
        }
        let r = *memo.get(&(root, Ctx::Arith))? as usize;
        out.truncate(r + 1);
        Some(out)
    }

    /// Whether node `i`, read in `ctx`, is an atom of a skeleton under `policy`.
    fn atom(&mut self, i: u32, ctx: Ctx, root: bool, policy: Policy) -> bool {
        match self.role[i as usize] {
            Role::Const | Role::Var => false,
            Role::Opaque => true,
            role => {
                if role == Role::Arith && ctx == Ctx::Bitwise {
                    return true;
                }
                let c = self.find(i);
                match policy {
                    Policy::Minimal | Policy::Linear => false,
                    Policy::Classes => !root && self.abstracted[c as usize],
                    Policy::Everything => self.abstracted[c as usize],
                }
            }
        }
    }

    /// The skeleton of node `root` (read as a term): atoms become variables of `vm`, one per
    /// class (the class's own variable when it has one).
    fn skeleton(&mut self, root: u32, policy: Policy, vm: &mut VarMap) -> Option<Vec<SkelNode>> {
        let mut out: Vec<SkelNode> = Vec::new();
        let mut memo: HashMap<(u32, Ctx), u32> = HashMap::new();
        let mut stack: Vec<(u32, Ctx, bool)> = vec![(root, Ctx::Arith, false)];
        while let Some((i, ctx, expanded)) = stack.pop() {
            if memo.contains_key(&(i, ctx)) {
                continue;
            }
            let n = self.nodes[i as usize];
            if !expanded {
                if let Some(c) = self.cst[i as usize] {
                    out.push(SkelNode::Const(c));
                } else if self.atom(i, ctx, i == root, policy) {
                    let c = self.find(i);
                    let v = match self.var_member[c as usize] {
                        Some(vi) => match self.nodes[vi as usize].op {
                            MOp::Var(x) => vm.orig(x, n.width),
                            _ => return None,
                        },
                        None => vm.class(c, n.width),
                    };
                    out.push(SkelNode::Var(v));
                } else if let MOp::Var(x) = n.op {
                    let v = vm.orig(x, n.width);
                    out.push(SkelNode::Var(v));
                } else {
                    let sub = match self.role[i as usize] {
                        Role::Bitwise => Ctx::Bitwise,
                        Role::Not => ctx,
                        _ => Ctx::Arith,
                    };
                    stack.push((i, ctx, true));
                    for &k in &n.args[..n.op.arity()] {
                        stack.push((k, sub, false));
                    }
                    continue;
                }
                memo.insert((i, ctx), out.len() as u32 - 1);
                continue;
            }
            let sub = match self.role[i as usize] {
                Role::Bitwise => Ctx::Bitwise,
                Role::Not => ctx,
                _ => Ctx::Arith,
            };
            let mut args = [0u32; 2];
            for (k, &a) in n.args[..n.op.arity()].iter().enumerate() {
                args[k] = *memo.get(&(a, sub))?;
            }
            out.push(SkelNode::Op(n.op, args));
            memo.insert((i, ctx), out.len() as u32 - 1);
        }
        // The root is the last node built for it.
        let r = *memo.get(&(root, Ctx::Arith))? as usize;
        out.truncate(r + 1);
        Some(out)
    }
}

// ----- carries -------------------------------------------------------------------------------

/// The most state bits (carries and shifted-out bits) a bit-serial comparison keeps.
const CARRY_BITS: u32 = 32;

/// The largest left shift a bit-serial comparison follows (its last bits are state).
const CARRY_SHIFT: u16 = 8;

/// One node of a bit-serial circuit: how its bit at a position is made.
#[derive(Copy, Clone)]
enum Serial {
    Const(BitVec),
    Var(u32),
    Not(usize),
    And(usize, usize),
    Or(usize, usize),
    Xor(usize, usize),
    /// `a + b + carry` (`sub`: `a + ~b + carry`, the carry starting at 1); the carry's state bit.
    Add(usize, usize, bool, u32),
    /// `~a + carry`, the carry starting at 1.
    Neg(usize, u32),
    /// `a << k`: the last `k` bits of `a` from state bit `at` on.
    Shl(usize, u16, u32),
}

/// Bit-serial comparison of expressions built from `+ − neg ~ & | ^`, constants, left shifts by
/// at most [`CARRY_SHIFT`] and products by a constant below `2^(CARRY_SHIFT + 1)` or its
/// negation (a sum of shifts), every node and variable of one width. Bit `j` of such an
/// expression depends only on bits `0..=j` of the variables (they are T-functions), through a
/// few bits of state: each addition's carry and each shift's last bits. So it is a finite
/// automaton reading one bit of every variable per position; walking every reachable state
/// through every input bit combination at every position, the two sides agree everywhere or a
/// path gives an input where they differ. Exact at the width, whatever carries propagate
/// (`(y + y) & y & −y` is 0: no bit of `y` both follows a set bit and has none below it). Up to
/// [`CARRY_BITS`] bits of state and six variables; charged as node evaluations.
pub(crate) fn carries<M: Meter>(
    meter: &mut M,
    a: &MbaExpr,
    b: &MbaExpr,
    report: &mut Report,
) -> Result<bool, M::Err> {
    let Some(w) = a.width() else {
        return Ok(false);
    };
    let t = a.vars().len();
    if b.width() != Some(w) || a.vars() != b.vars() || t > 6 || a.vars().iter().any(|&v| v != w) {
        return Ok(false);
    }
    // Both sides as one circuit (live nodes only, equal ones once: they share their state).
    let mut circuit: Vec<Serial> = Vec::new();
    let mut state = 0u32;
    let mut roots = [0usize; 2];
    let mut interned: HashMap<(MOp, [usize; 2]), usize> = HashMap::new();
    for (side, m) in [a, b].into_iter().enumerate() {
        let live = live(m);
        let mut map: Vec<usize> = vec![usize::MAX; m.nodes().len()];
        for (i, n) in m.nodes().iter().enumerate() {
            if !live[i] {
                continue;
            }
            if n.width != w {
                return Ok(false);
            }
            let mut key = [0usize; 2];
            for (k, slot) in key.iter_mut().enumerate().take(n.op.arity()) {
                *slot = map[n.args[k] as usize];
            }
            if commutative(&n.op) && key[0] > key[1] {
                key.swap(0, 1);
            }
            if let Some(&c) = interned.get(&(n.op, key)) {
                map[i] = c;
                continue;
            }
            let x = |k: usize| key[k];
            let s = match n.op {
                MOp::Const(c) => Serial::Const(c),
                MOp::Var(v) => Serial::Var(v),
                MOp::Not => Serial::Not(x(0)),
                MOp::And => Serial::And(x(0), x(1)),
                MOp::Or => Serial::Or(x(0), x(1)),
                MOp::Xor => Serial::Xor(x(0), x(1)),
                MOp::Add | MOp::Sub => {
                    state += 1;
                    Serial::Add(x(0), x(1), n.op == MOp::Sub, state - 1)
                }
                MOp::Neg => {
                    state += 1;
                    Serial::Neg(x(0), state - 1)
                }
                // `t << 0` is `t` (a shift keeps its last `k` bits as state: none here).
                MOp::Shl(0) => {
                    map[i] = x(0);
                    interned.insert((n.op, key), map[i]);
                    continue;
                }
                MOp::Shl(k) if k <= CARRY_SHIFT => {
                    state += u32::from(k);
                    Serial::Shl(x(0), k, state - u32::from(k))
                }
                // `t·c` for a constant `c` (or `−c`) of few low bits: the sum of `t << i` over
                // its set bits (negated), whichever of the two takes fewer state bits.
                MOp::Mul => {
                    let (t, c) = match (&circuit[x(0)], &circuit[x(1)]) {
                        (_, Serial::Const(c)) => (x(0), *c),
                        (Serial::Const(c), _) => (x(1), *c),
                        _ => return Ok(false),
                    };
                    // The state bits of the expansion: the shifts' amounts and one per add.
                    let bits = |c: &BitVec| {
                        c.to_u64()
                            .filter(|&v| v < 1u64 << (u32::from(CARRY_SHIFT) + 1))
                            .map(|v| {
                                (0..=u32::from(CARRY_SHIFT))
                                    .filter(|&i| v >> i & 1 == 1)
                                    .map(|i| i + 1)
                                    .sum::<u32>()
                                    .saturating_sub(1)
                            })
                    };
                    let neg = BitVec::un_unchecked(UnOp::Neg, &c);
                    let (c, negate) = match (bits(&c), bits(&neg)) {
                        (Some(p), Some(n)) if n + 1 < p => (neg, true),
                        (Some(_), _) => (c, false),
                        (None, Some(_)) => (neg, true),
                        (None, None) => return Ok(false),
                    };
                    let v = c.to_u64().unwrap_or(0);
                    let mut acc: Option<usize> = None;
                    for i in 0..=CARRY_SHIFT {
                        if v >> i & 1 == 0 {
                            continue;
                        }
                        let part = if i == 0 {
                            t
                        } else {
                            state += u32::from(i);
                            circuit.push(Serial::Shl(t, i, state - u32::from(i)));
                            circuit.len() - 1
                        };
                        acc = Some(match acc {
                            None => part,
                            Some(a) => {
                                state += 1;
                                circuit.push(Serial::Add(a, part, false, state - 1));
                                circuit.len() - 1
                            }
                        });
                    }
                    let Some(acc) = acc else {
                        // A product by 0 is 0.
                        circuit.push(Serial::Const(BitVec::zero(w)));
                        map[i] = circuit.len() - 1;
                        interned.insert((n.op, key), map[i]);
                        continue;
                    };
                    if state > CARRY_BITS {
                        return Ok(false);
                    }
                    if negate {
                        state += 1;
                        Serial::Neg(acc, state - 1)
                    } else {
                        map[i] = acc;
                        interned.insert((n.op, key), acc);
                        continue;
                    }
                }
                _ => return Ok(false),
            };
            if state > CARRY_BITS {
                return Ok(false);
            }
            circuit.push(s);
            map[i] = circuit.len() - 1;
            interned.insert((n.op, key), map[i]);
        }
        roots[side] = map[nodes_root(m)];
    }
    // The initial state: carries of subtractions and negations are 1.
    let mut init = 0u64;
    for s in &circuit {
        match *s {
            Serial::Add(_, _, true, at) | Serial::Neg(_, at) => init |= 1 << at,
            _ => {}
        }
    }
    let inputs = 1u64 << t;
    let mut layer: Vec<u64> = vec![init];
    // Per position: each state's predecessor and input (for a counterexample).
    let mut trail: Vec<HashMap<u64, (u64, u64)>> = Vec::new();
    let mut bits = vec![false; circuit.len()];
    // The states that occur are usually few, so the test is sized as it goes: past
    // [`MAX_EFFORT`] in all it is a stable decline (the same states occur whatever the budget);
    // a position over what is left of the budget is not run.
    let mut effort = 0u64;
    for j in 0..w.bits() {
        let units = (layer.len() as u64) * inputs * circuit.len() as u64;
        effort = effort.saturating_add(units);
        if effort > MAX_EFFORT {
            return Ok(false);
        }
        if units > meter.left() {
            report.over_budget = true;
            return Ok(false);
        }
        meter.charge(units)?;
        report.points += layer.len() as u64 * inputs;
        let mut next: HashMap<u64, (u64, u64)> = HashMap::new();
        for &st in &layer {
            for x in 0..inputs {
                let mut out = st;
                for (k, s) in circuit.iter().enumerate() {
                    bits[k] = match *s {
                        Serial::Const(c) => c.bit(j).unwrap_or(false),
                        Serial::Var(v) => x >> v & 1 == 1,
                        Serial::Not(p) => !bits[p],
                        Serial::And(p, q) => bits[p] & bits[q],
                        Serial::Or(p, q) => bits[p] | bits[q],
                        Serial::Xor(p, q) => bits[p] ^ bits[q],
                        Serial::Add(p, q, sub, at) => {
                            let (u, v, c) = (bits[p], bits[q] ^ sub, st >> at & 1 == 1);
                            let carry = (u & v) | (u & c) | (v & c);
                            out = (out & !(1 << at)) | (u64::from(carry) << at);
                            u ^ v ^ c
                        }
                        Serial::Neg(p, at) => {
                            let (u, c) = (!bits[p], st >> at & 1 == 1);
                            out = (out & !(1 << at)) | (u64::from(u & c) << at);
                            u ^ c
                        }
                        Serial::Shl(p, k, at) => {
                            // Bit j − k of the operand is the oldest kept; the current one
                            // enters.
                            let hist = (st >> at) & ((1u64 << k) - 1);
                            let oldest = hist >> (k - 1) & 1 == 1;
                            let newer = ((hist << 1) | u64::from(bits[p])) & ((1u64 << k) - 1);
                            out = (out & !(((1u64 << k) - 1) << at)) | (newer << at);
                            oldest
                        }
                    };
                }
                if bits[roots[0]] != bits[roots[1]] {
                    // An input where the sides differ: bits along the path, 0 above.
                    let mut vals = vec![0u64; t];
                    let mut cur = (st, x);
                    for pos in (0..=usize::from(j)).rev() {
                        for (v, val) in vals.iter_mut().enumerate() {
                            *val |= (cur.1 >> v & 1) << pos;
                        }
                        if pos > 0 {
                            cur = trail[pos - 1][&cur.0];
                        }
                    }
                    if w.bits() > 64 {
                        // Only positions below 64 are rebuilt: undecided rather than wrong.
                        return Ok(false);
                    }
                    report.verdict = Verdict::Refuted;
                    report.cert = Some(Cert::Carries);
                    report.counterexample = Some(
                        vals.iter()
                            .map(|&v| BitVec::wrapping_from_u64(w, v))
                            .collect(),
                    );
                    return Ok(true);
                }
                next.entry(out).or_insert((st, x));
            }
        }
        layer = next.keys().copied().collect();
        layer.sort_unstable();
        trail.push(next);
    }
    report.verdict = Verdict::Proved;
    report.cert = Some(Cert::Carries);
    Ok(true)
}

/// The root of `m` (its last node).
fn nodes_root(m: &MbaExpr) -> usize {
    m.nodes().len().saturating_sub(1)
}

// ----- symbolic ------------------------------------------------------------------------------

/// The most monomials a symbolic expansion keeps (more: it decides nothing).
const SYMBOLIC_TERMS: usize = 4096;

/// A polynomial over symbols: monomials (symbol ids, sorted, repeated for powers) with
/// coefficients of one width.
#[derive(Clone, Debug, PartialEq, Eq)]
struct SymPoly(std::collections::BTreeMap<Vec<u32>, BitVec>);

impl SymPoly {
    fn constant(c: BitVec) -> SymPoly {
        let mut m = std::collections::BTreeMap::new();
        if !c.is_zero() {
            m.insert(Vec::new(), c);
        }
        SymPoly(m)
    }

    fn symbol(s: u32, w: Width) -> SymPoly {
        let mut m = std::collections::BTreeMap::new();
        m.insert(vec![s], BitVec::one(w));
        SymPoly(m)
    }

    fn add_term(&mut self, m: Vec<u32>, c: &BitVec) {
        if c.is_zero() {
            return;
        }
        match self.0.entry(m) {
            std::collections::btree_map::Entry::Vacant(v) => {
                v.insert(*c);
            }
            std::collections::btree_map::Entry::Occupied(mut o) => {
                let s = BitVec::bin_unchecked(BinOp::Add, o.get(), c);
                if s.is_zero() {
                    o.remove();
                } else {
                    *o.get_mut() = s;
                }
            }
        }
    }

    fn add(&self, o: &SymPoly, k: &BitVec) -> SymPoly {
        let mut out = self.clone();
        for (m, c) in &o.0 {
            out.add_term(m.clone(), &BitVec::bin_unchecked(BinOp::Mul, c, k));
        }
        out
    }

    fn mul(&self, o: &SymPoly) -> Option<SymPoly> {
        if self.0.len().saturating_mul(o.0.len()) > SYMBOLIC_TERMS * 4 {
            return None;
        }
        let mut out = SymPoly(std::collections::BTreeMap::new());
        for (m, c) in &self.0 {
            for (n, d) in &o.0 {
                let mut mn: Vec<u32> = m.iter().chain(n).copied().collect();
                mn.sort_unstable();
                out.add_term(mn, &BitVec::bin_unchecked(BinOp::Mul, c, d));
            }
        }
        (out.0.len() <= SYMBOLIC_TERMS).then_some(out)
    }
}

/// Whether `a` and `b` are the same polynomial over symbols: variables; the conjunctions of the
/// leaves of a bitwise function whose constants are 0 or all-ones, which it is read as by its
/// integer expansion (`x | y` is `x + y − (x & y)`, every bit alike); and any other bitwise
/// subterm, one symbol by its structure. Equal polynomials are equal functions, whatever the
/// symbols' values (so for their actual ones); unequal ones decide nothing. `None` past
/// [`SYMBOLIC_TERMS`]. Work: one unit per monomial operation.
pub(crate) fn symbolic_equal(a: &MbaExpr, b: &MbaExpr, work: &mut u64) -> Option<bool> {
    let w = a.width()?;
    if b.width()? != w || a.vars() != b.vars() {
        return None;
    }
    // Both sides in one hash-consed table, so equal subterms are one symbol.
    let mut canon: HashMap<MNode, u32> = HashMap::new();
    let mut nodes: Vec<MNode> = Vec::new();
    let mut roots = [0u32; 2];
    for (side, m) in [a, b].into_iter().enumerate() {
        let mut map: Vec<u32> = Vec::with_capacity(m.nodes().len());
        for n in m.nodes() {
            let mut k = *n;
            for i in 0..n.op.arity() {
                k.args[i] = map[n.args[i] as usize];
            }
            if commutative(&k.op) && k.args[0] > k.args[1] {
                k.args.swap(0, 1);
            }
            let id = *canon.entry(k).or_insert_with(|| {
                nodes.push(k);
                nodes.len() as u32 - 1
            });
            map.push(id);
        }
        roots[side] = *map.last()?;
    }
    let cst = constants(&nodes);
    let bitwise = |op: &MOp| matches!(op, MOp::And | MOp::Or | MOp::Xor | MOp::Not);
    // Symbols: variables by index, conjunctions by their leaf set, others by node.
    let mut symbols: HashMap<(u8, Vec<u32>), u32> = HashMap::new();
    let mut symbol = |kind: u8, key: Vec<u32>| {
        let n = symbols.len() as u32;
        *symbols.entry((kind, key)).or_insert(n)
    };
    let mut polys: Vec<Option<SymPoly>> = vec![None; nodes.len()];
    for i in 0..nodes.len() {
        let n = nodes[i];
        let arg = |k: usize| polys[n.args[k] as usize].clone();
        let p = if let Some(c) = cst[i] {
            SymPoly::constant(c)
        } else {
            match n.op {
                MOp::Var(v) => SymPoly::symbol(symbol(0, vec![v]), w),
                MOp::Add => arg(0)?.add(&arg(1)?, &BitVec::one(w)),
                MOp::Sub => arg(0)?.add(&arg(1)?, &BitVec::ones(w)),
                MOp::Neg => SymPoly::constant(BitVec::zero(w)).add(&arg(0)?, &BitVec::ones(w)),
                MOp::Shl(k) => {
                    let s = crate::facts::known::bv_shl(&BitVec::one(w), u32::from(k));
                    SymPoly::constant(BitVec::zero(w)).add(&arg(0)?, &s)
                }
                MOp::Mul => {
                    let (x, y) = (arg(0)?, arg(1)?);
                    *work = work.saturating_add((x.0.len() * y.0.len()) as u64);
                    x.mul(&y)?
                }
                MOp::And | MOp::Or | MOp::Xor | MOp::Not => {
                    // The bitwise function's leaves: variables and non-bitwise subterms.
                    let mut leaves: Vec<u32> = Vec::new();
                    let mut uniform = true;
                    let mut stack = vec![i as u32];
                    let mut seen: HashMap<u32, ()> = HashMap::new();
                    while let Some(k) = stack.pop() {
                        if seen.insert(k, ()).is_some() {
                            continue;
                        }
                        let m = nodes[k as usize];
                        if let Some(c) = cst[k as usize] {
                            uniform &= c.is_zero() || c.is_ones();
                        } else if bitwise(&m.op) {
                            stack.extend(m.args[..m.op.arity()].iter().copied());
                        } else if !leaves.contains(&k) {
                            leaves.push(k);
                        }
                    }
                    leaves.sort_unstable();
                    let expansion = if uniform && leaves.len() <= 6 {
                        // Its table over the leaves, then its Möbius expansion.
                        let t = leaves.len();
                        let full: u64 = if t == 6 {
                            u64::MAX
                        } else {
                            (1u64 << (1u32 << t)) - 1
                        };
                        let mut table: HashMap<u32, u64> = HashMap::new();
                        let mut order: Vec<u32> = seen.keys().copied().collect();
                        order.sort_unstable();
                        for &k in &order {
                            let m = nodes[k as usize];
                            let v = if let Some(c) = cst[k as usize] {
                                if c.is_zero() { 0 } else { full }
                            } else if let Some(j) = leaves.iter().position(|&l| l == k) {
                                (0..1u64 << t)
                                    .filter(|e| e >> j & 1 == 1)
                                    .fold(0u64, |acc, e| acc | 1 << e)
                            } else {
                                let x = |a: usize| table.get(&m.args[a]).copied();
                                match m.op {
                                    MOp::Not => !x(0)? & full,
                                    MOp::And => x(0)? & x(1)?,
                                    MOp::Or => x(0)? | x(1)?,
                                    _ => x(0)? ^ x(1)?,
                                }
                            };
                            table.insert(k, v);
                        }
                        let f = *table.get(&(i as u32))?;
                        let mut coef: Vec<i64> =
                            (0..1usize << t).map(|e| (f >> e & 1) as i64).collect();
                        for bit in 0..t {
                            for e in 0..1usize << t {
                                if e >> bit & 1 == 1 {
                                    coef[e] -= coef[e ^ 1 << bit];
                                }
                            }
                        }
                        // The leaves' own polynomials, as symbols where they are not variables.
                        let mut leaf_sym: Vec<u32> = Vec::with_capacity(t);
                        for &l in &leaves {
                            leaf_sym.push(match nodes[l as usize].op {
                                MOp::Var(v) => symbol(0, vec![v]),
                                _ => symbol(2, vec![l]),
                            });
                        }
                        let mut p =
                            SymPoly::constant(BitVec::wrapping_from_i128(w, -i128::from(coef[0])));
                        for (e, &c) in coef.iter().enumerate().skip(1) {
                            if c == 0 {
                                continue;
                            }
                            let c = BitVec::wrapping_from_i128(w, i128::from(c));
                            if e.count_ones() == 1 {
                                // A lone leaf is its own value: its polynomial.
                                let l = leaves[e.trailing_zeros() as usize];
                                p = p.add(polys[l as usize].as_ref()?, &c);
                                continue;
                            }
                            let mut set: Vec<u32> = (0..t)
                                .filter(|&j| e >> j & 1 == 1)
                                .map(|j| leaf_sym[j])
                                .collect();
                            set.sort_unstable();
                            p.add_term(vec![symbol(1, set)], &c);
                        }
                        Some(p)
                    } else {
                        None
                    };
                    // A non-variable leaf stands for its own polynomial only through its
                    // symbol; the whole is one symbol when it is not expanded.
                    expansion.unwrap_or_else(|| SymPoly::symbol(symbol(2, vec![i as u32]), w))
                }
                _ => SymPoly::symbol(symbol(2, vec![i as u32]), w),
            }
        };
        *work = work.saturating_add(p.0.len() as u64 + 1);
        polys[i] = Some(p);
    }
    let (pa, pb) = (
        polys[roots[0] as usize].as_ref()?,
        polys[roots[1] as usize].as_ref()?,
    );
    Some(pa == pb)
}

/// [`symbolic_equal`], charged to `meter` (a unit per monomial operation, at most what is
/// left): true only for a proof, which it records.
fn symbolic<M: Meter>(
    meter: &mut M,
    a: &MbaExpr,
    b: &MbaExpr,
    report: &mut Report,
) -> Result<bool, M::Err> {
    let mut work = 0u64;
    let equal = symbolic_equal(a, b, &mut work) == Some(true);
    meter.charge(work.min(meter.left()))?;
    if equal {
        report.verdict = Verdict::Proved;
        report.cert = Some(Cert::Symbolic);
    }
    Ok(equal)
}

/// `m` with variable `v` read as `by` (over the same variables): `by`'s nodes, then `m`'s
/// nodes that its root uses, `v` mapped to `by`'s root.
fn substitute_var(m: &MbaExpr, v: u32, by: &MbaExpr) -> Option<MbaExpr> {
    let nodes = m.nodes();
    let live = live(m);
    let mut out = MbaExpr::new(m.vars().to_vec());
    let mut map_by: Vec<u32> = Vec::with_capacity(by.nodes().len());
    for n in by.nodes() {
        let args: Vec<u32> = n.args[..n.op.arity()]
            .iter()
            .map(|&a| map_by[a as usize])
            .collect();
        map_by.push(out.push(n.op, &args).ok()?);
    }
    let by_root = *map_by.last()?;
    let mut map: Vec<u32> = vec![0; nodes.len()];
    let mut last = by_root;
    for (i, n) in nodes.iter().enumerate() {
        if !live[i] {
            continue;
        }
        last = match n.op {
            MOp::Var(x) if x == v => by_root,
            op => {
                let args: Vec<u32> = n.args[..op.arity()]
                    .iter()
                    .map(|&a| map[a as usize])
                    .collect();
                out.push(op, &args).ok()?
            }
        };
        map[i] = last;
    }
    // The root is the last node (a root that is `v` itself is `by`'s root, pushed last when
    // nothing else is live).
    if last as usize + 1 != out.nodes().len() {
        return None;
    }
    Some(out)
}

/// A bitwise function read arithmetically, as `konst + Σ c·(leaves read so, and-ed)`.
struct Expansion {
    width: Width,
    konst: BitVec,
    terms: Vec<(BitVec, Vec<(u32, Ctx)>)>,
}

/// A skeleton node before its variables are numbered.
#[derive(Clone, Debug)]
enum SkelNode {
    Const(BitVec),
    Var(u32),
    Op(MOp, [u32; 2]),
}

/// The variables of a pair of skeletons: original variables and atom classes.
#[derive(Default)]
struct VarMap {
    slots: Vec<(Slot, Width)>,
    /// Some atom class got a variable of its own.
    abstracted: bool,
}

#[derive(Copy, Clone, PartialEq, Eq)]
enum Slot {
    Orig(u32),
    Class(u32),
}

impl VarMap {
    fn get(&mut self, s: Slot, w: Width) -> u32 {
        if let Some(i) = self.slots.iter().position(|&(t, _)| t == s) {
            return i as u32;
        }
        self.slots.push((s, w));
        self.slots.len() as u32 - 1
    }

    fn orig(&mut self, v: u32, w: Width) -> u32 {
        self.get(Slot::Orig(v), w)
    }

    fn class(&mut self, c: u32, w: Width) -> u32 {
        self.abstracted = true;
        self.get(Slot::Class(c), w)
    }

    /// The skeleton as an expression over every variable of the map, all of width `w`.
    fn expr(&self, s: &[SkelNode], w: Width) -> Option<MbaExpr> {
        if self.slots.iter().any(|&(_, sw)| sw != w) {
            return None;
        }
        let mut m = MbaExpr::new(vec![w; self.slots.len()]);
        for n in s {
            match n {
                SkelNode::Const(c) => m.push(MOp::Const(*c), &[]),
                SkelNode::Var(v) => m.push(MOp::Var(*v), &[]),
                SkelNode::Op(op, args) => m.push(*op, &args[..op.arity()]),
            }
            .ok()?;
        }
        Some(m)
    }
}

/// Per node of `prog` (every node kept): a digest of its value at each point (the value itself
/// up to 64 bits). Equal values give equal digests.
fn digests(prog: &Program, points: &[Vec<BitVec>], nodes: usize) -> Vec<Vec<u64>> {
    match Kind::of(prog.widest()) {
        Kind::N64 => digests_in::<u64>(prog, points, nodes, |x| *x),
        Kind::N128 => digests_in::<u128>(prog, points, nodes, |x| {
            crate::hash::combine(*x as u64, (*x >> 64) as u64)
        }),
        Kind::Wide => digests_in::<Wide>(prog, points, nodes, |x| {
            x.0.iter().fold(0x5eed, |h, &l| crate::hash::combine(h, l))
        }),
    }
}

fn digests_in<L: Lane>(
    prog: &Program,
    points: &[Vec<BitVec>],
    nodes: usize,
    digest: impl Fn(&L) -> u64,
) -> Vec<Vec<u64>> {
    let n = points.len();
    let nv = points.first().map_or(0, Vec::len);
    let inputs: Vec<Vec<L>> = (0..nv)
        .map(|v| points.iter().map(|p| L::from_bv(&p[v])).collect())
        .collect();
    let mut regs: Vec<Vec<L>> = Vec::new();
    prog.run(&mut regs, &inputs, n);
    (0..nodes)
        .map(|i| match prog.reg_of(i) {
            Some(r) => regs[r][..n].iter().map(&digest).collect(),
            None => Vec::new(),
        })
        .collect()
}

// ----- the native prover -----------------------------------------------------------------------

/// bitwright's own exact equivalence checks as an [`EquivalenceProver`]: the refutation sample,
/// then the cheapest certificate that applies (the corner signature, single bit positions, at
/// most `d` bit positions for degree `d`, the pure-polynomial grid, exhaustive evaluation), over
/// abstracted atoms when a side leaves the polynomial fragment. The same checks are the evidence
/// gate's own, so an engine needs this prover only when its host uses the MBA module directly.
///
/// Work is counted in node evaluations against [`MbaBudget::steps`]; a certificate over the
/// budget is not run (`Unknown`). `Refuted` comes with a concrete counterexample.
///
/// ```
/// use bitwright::mba::{EquivalenceProver, MOp, MbaBudget, MbaExpr, NativeProver, Verdict};
/// use bitwright::Width;
///
/// // (x & y)·(x | y) + (x & ~y)·(~x & y) == x·y, a degree-2 identity, at 64 bits.
/// let w = Width::W64;
/// let mut a = MbaExpr::new(vec![w, w]);
/// let (x, y) = (a.push(MOp::Var(0), &[])?, a.push(MOp::Var(1), &[])?);
/// let (and, or) = (a.push(MOp::And, &[x, y])?, a.push(MOp::Or, &[x, y])?);
/// let p = a.push(MOp::Mul, &[and, or])?;
/// let (nx, ny) = (a.push(MOp::Not, &[x])?, a.push(MOp::Not, &[y])?);
/// let (l, r) = (a.push(MOp::And, &[x, ny])?, a.push(MOp::And, &[nx, y])?);
/// let q = a.push(MOp::Mul, &[l, r])?;
/// a.push(MOp::Add, &[p, q])?;
/// let mut b = MbaExpr::new(vec![w, w]);
/// let (x, y) = (b.push(MOp::Var(0), &[])?, b.push(MOp::Var(1), &[])?);
/// b.push(MOp::Mul, &[x, y])?;
/// let prover = NativeProver::default();
/// assert_eq!(prover.prove_equal(&a, &b, &MbaBudget::default()), Verdict::Proved);
/// assert_eq!(prover.stats().sparse, 1);
/// # Ok::<(), bitwright::mba::MbaError>(())
/// ```
///
/// [`EquivalenceProver`]: super::EquivalenceProver
/// [`MbaBudget::steps`]: super::MbaBudget::steps
#[derive(Debug, Default)]
pub struct NativeProver {
    stats: std::sync::Mutex<CertStats>,
}

impl NativeProver {
    /// A prover with zeroed counters.
    pub fn new() -> NativeProver {
        NativeProver::default()
    }

    /// What it has decided so far, and how.
    pub fn stats(&self) -> CertStats {
        self.stats.lock().map_or_else(|e| *e.into_inner(), |g| *g)
    }
}

impl super::EquivalenceProver for NativeProver {
    fn id(&self) -> &str {
        "bitwright.native.v2"
    }

    fn prove_equal(&self, a: &MbaExpr, b: &MbaExpr, budget: &super::MbaBudget) -> Verdict {
        let report = check(a, b, budget.steps);
        if let Ok(mut s) = self.stats.lock() {
            s.record(&report);
        }
        report.verdict
    }
}

/// The refutation sample, then [`prove`], under a budget of `steps` node evaluations (the
/// report says how many it spent).
pub(crate) fn check(a: &MbaExpr, b: &MbaExpr, steps: u64) -> Report {
    let mut meter = Steps::new(steps);
    let mut report = Report::new();
    if a.vars() != b.vars() || a.width().is_none() || a.width() != b.width() {
        return report;
    }
    let units = ((a.nodes().len() + b.nodes().len()) * SAMPLE_POINTS) as u64;
    if meter.charge(units).is_err() {
        report.over_budget = true;
        return report;
    }
    report.points += SAMPLE_POINTS as u64;
    report.work = meter.spent;
    let seed = crate::hash::combine(a.key()[0], b.key()[1]);
    let points = sample_points(a.vars(), &[a, b], seed);
    if let Some(p) = refute(a, b, &points) {
        report.verdict = Verdict::Refuted;
        report.counterexample = Some(p);
        return report;
    }
    let mut r = match prove(a, b, &mut meter) {
        Ok(mut r) => {
            r.points += report.points;
            r
        }
        Err(()) => {
            report.over_budget = true;
            report
        }
    };
    r.work = meter.spent;
    r
}
