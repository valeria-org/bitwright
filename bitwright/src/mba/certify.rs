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

/// Exhaustive evaluation is a test up to this many variable bits.
pub(crate) const EXHAUSTIVE_BITS: u32 = 20;

/// The signature test takes at most this many variables.
const SIGNATURE_VARS: usize = 16;

/// Points of the refutation sample.
pub(crate) const SAMPLE_POINTS: usize = 64;

/// The most proof attempts per atom when atoms are paired by their definitions.
const PAIR_TRIES: usize = 4;

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
    /// Points evaluated, over every test run.
    pub(crate) points: u64,
    /// A test was skipped for lack of budget (more budget might decide).
    pub(crate) over_budget: bool,
    /// Internal inconsistencies seen (a pairing that disagreed at a sample point); never
    /// expected.
    pub(crate) internal: u64,
    /// For `Refuted`: an input where the sides differ (one value per variable).
    pub(crate) counterexample: Option<Vec<BitVec>>,
}

impl Report {
    fn new() -> Report {
        Report {
            verdict: Verdict::Unknown,
            cert: None,
            compositional: false,
            points: 0,
            over_budget: false,
            internal: 0,
            counterexample: None,
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
fn constants(nodes: &[MNode]) -> Vec<Option<BitVec>> {
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
            c.clear();
        }
        let mut n = 0;
        while n < BLOCK && !self.done {
            for (v, col) in cols.iter_mut().enumerate() {
                let _ = v;
                col.push(L::default());
            }
            match self.cert {
                Cert::Signature => {
                    for (j, &v) in used.iter().enumerate() {
                        cols[v][n] = if self.next >> j & 1 == 1 {
                            L::not(L::default(), masks[v])
                        } else {
                            L::default()
                        };
                    }
                    self.next += 1;
                    self.done = self.next >= self.total;
                }
                Cert::Exhaustive => {
                    let mut rest = self.next;
                    for &v in used {
                        let bits = vars[v].bits();
                        let x = rest & ((1u64 << bits) - 1);
                        rest >>= bits;
                        cols[v][n] = L::small(x, masks[v]);
                    }
                    self.next += 1;
                    self.done = self.next >= self.total;
                }
                Cert::Grid => {
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
                }
                Cert::SingleBit | Cert::Sparse => {
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
                }
            }
            n += 1;
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
    if plan.points > MAX_POINTS {
        return Ok(Run::TooBig);
    }
    let per = (pa.len() + pb.len()) as u64;
    if plan.points.saturating_mul(per) > meter.left() {
        report.over_budget = true;
        return Ok(Run::OverBudget);
    }
    let width = a.width().map_or(1, |w| w.bits());
    match Kind::of(pa.widest().max(pb.widest())) {
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

/// Decides `a == b` (on every input) if one of the tests applies within the budget. `Refuted`
/// only with a concrete input where they differ; `Unknown` when no test applies, a test is
/// over the budget, or only skeletons over abstracted atoms were found to differ. Expressions
/// over different variables or of different widths are not compared (`Unknown`).
pub(crate) fn prove<M: Meter>(a: &MbaExpr, b: &MbaExpr, meter: &mut M) -> Result<Report, M::Err> {
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
    if let Some(p) = plan(a, &pa, &pb) {
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
                // Abstraction never makes a polynomial test smaller; only a non-polynomial
                // side needs it.
                if pa.poly && pb.poly {
                    return Ok(report);
                }
            }
        }
    }
    Compose::new(a, b).prove(meter, &mut report)?;
    Ok(report)
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
}

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
            .map(|(n, c)| match n.op {
                _ if c.is_some() => Role::Const,
                MOp::Var(_) => Role::Var,
                MOp::And | MOp::Or | MOp::Xor => Role::Bitwise,
                MOp::Not => Role::Not,
                MOp::Add | MOp::Sub | MOp::Mul | MOp::Neg | MOp::Shl(_) => Role::Arith,
                _ => Role::Opaque,
            })
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
        };
        c.mark_forced();
        c
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
        let digests = digests(&prog, &points, self.nodes.len());
        let (ra, rb) = (self.root_a as usize, self.root_b as usize);
        if let Some(p) = (0..points.len()).find(|&p| digests[ra][p] != digests[rb][p]) {
            // A real input where the sides differ.
            report.verdict = Verdict::Refuted;
            report.counterexample = Some(points[p].clone());
            return Ok(());
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
        for policy in [Policy::Minimal, Policy::Classes, Policy::Everything] {
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
        for policy in [Policy::Minimal, Policy::Classes, Policy::Everything] {
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
        let (Some(sx), Some(sy)) = (
            self.skeleton(x, policy, &mut vm),
            self.skeleton(y, policy, &mut vm),
        ) else {
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
        let Some(p) = plan(&a, &pa, &pb) else {
            return Ok((None, None));
        };
        Ok(match run(meter, &a, &b, &p, report)? {
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
                    Policy::Minimal => false,
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
        "bitwright.native.v1"
    }

    fn prove_equal(&self, a: &MbaExpr, b: &MbaExpr, budget: &super::MbaBudget) -> Verdict {
        let report = check(a, b, budget.steps);
        if let Ok(mut s) = self.stats.lock() {
            s.record(&report);
        }
        report.verdict
    }
}

/// The refutation sample, then [`prove`], under a budget of `steps` node evaluations.
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
    let seed = crate::hash::combine(a.key()[0], b.key()[1]);
    let points = sample_points(a.vars(), &[a, b], seed);
    if refute(a, b, &points).is_some() {
        report.verdict = Verdict::Refuted;
        return report;
    }
    match prove(a, b, &mut meter) {
        Ok(mut r) => {
            r.points += report.points;
            r
        }
        Err(()) => {
            report.over_budget = true;
            report
        }
    }
}
