//! Synthesis: the smallest expression equal to a given one, over its variables and constants,
//! whatever its shape (MBA or not). Bottom-up enumeration by size, one representative per
//! behavior on a set of sample points (observational equivalence: Udupa et al., PLDI 2013;
//! Alur et al., TACAS 2017), and counterexample-guided inductive synthesis (Solar-Lezama et
//! al., ASPLOS 2006): a candidate that behaves like the target on every sample is proved equal
//! by the native prover, and a counterexample becomes a sample and the enumeration starts over.
//! Every answer is proved, each proof within [`Config::conflicts`] and
//! [`Config::propagations`]; [`synthesize_report`] also names the candidates whose proofs those
//! budgets left undecided. Feature `prove`.
//!
//! ```
//! use bitwright::{Context, ParseOptions, Width};
//! use bitwright::synth::{Config, synthesize};
//!
//! let mut cx = Context::new();
//! let e = cx.parse("(x | y) + (x & y) - x", &ParseOptions::width(Width::W32))?;
//! let s = synthesize(&mut cx, e, &Config::default())?.expect("a smaller expression");
//! assert_eq!(cx.display(s).to_string(), "y");
//! # Ok::<(), bitwright::Error>(())
//! ```

use std::collections::HashMap;

use crate::prove::{self, Outcome};
use crate::{BinOp, BitVec, CmpOp, Context, Error, Expr, SymbolKey, UnOp, View, Width};

/// How far to search.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct Config {
    /// The largest candidate, in nodes (a tree: leaves and operators).
    pub max_size: u8,
    /// The most distinct behaviors kept (memory: each costs a word per sample).
    pub max_terms: usize,
    /// Random sample points (besides boundary values).
    pub samples: usize,
    /// The SAT solver's conflict budget for each proof; a candidate whose proof needs more is
    /// left unproved ([`Report::unproved`]).
    pub conflicts: u64,
    /// The SAT solver's propagation budget for each proof (`u64::MAX`, the default: no limit),
    /// likewise. A conflict costs more propagation on a larger circuit, so this bounds the time
    /// a proof takes more closely than [`conflicts`](Self::conflicts) does, and as
    /// deterministically.
    pub propagations: u64,
    /// How many counterexamples may restart the search.
    pub restarts: usize,
    /// At most this many variables.
    pub max_vars: usize,
    /// Whether candidates may hold comparisons (`== != <u <s`, each the value 0 or 1 at the
    /// target's width; a comparison counts one node, its extension none). On by default:
    /// `(x | -x) >>u 63` is `x != 0`, and a sum with a correction where a value is zero has
    /// no smaller writing without one. The enumeration is about a third larger with them.
    pub comparisons: bool,
}

impl Default for Config {
    fn default() -> Self {
        Config {
            max_size: 7,
            max_terms: 400_000,
            samples: 24,
            conflicts: 200_000,
            propagations: u64::MAX,
            restarts: 8,
            max_vars: 4,
            comparisons: true,
        }
    }
}

setters!(Config {
    with_max_size: max_size: u8,
    with_max_terms: max_terms: usize,
    with_samples: samples: usize,
    with_conflicts: conflicts: u64,
    with_propagations: propagations: u64,
    with_restarts: restarts: usize,
    with_max_vars: max_vars: usize,
    with_comparisons: comparisons: bool,
});

const UNARY: [UnOp; 2] = [UnOp::Not, UnOp::Neg];
const BINARY: [BinOp; 11] = [
    BinOp::Add,
    BinOp::Sub,
    BinOp::Mul,
    BinOp::And,
    BinOp::Or,
    BinOp::Xor,
    BinOp::Shl,
    BinOp::LShr,
    BinOp::AShr,
    BinOp::UDiv,
    BinOp::URem,
];

/// The comparisons of candidates: the others are these with the operands exchanged, or one
/// more node (`a <=u b` is `1 ^ (b <u a)`).
const COMPARE: [CmpOp; 4] = [CmpOp::Eq, CmpOp::Ne, CmpOp::Ult, CmpOp::Slt];

/// The most pairs of terms tried as a candidate in one round (see `Search::pairs`).
const MAX_PAIRS: usize = 64;

fn commutative(op: BinOp) -> bool {
    matches!(
        op,
        BinOp::Add | BinOp::Mul | BinOp::And | BinOp::Or | BinOp::Xor
    )
}

#[derive(Copy, Clone, Debug)]
enum Term {
    Var(usize),
    Const(u64),
    Un(UnOp, u32),
    Bin(BinOp, u32, u32),
    /// A comparison, zero-extended to the target's width.
    Cmp(CmpOp, u32, u32),
}

/// Values of width `w` in the low bits of a `u64`, and the operators on them, as bitwright
/// defines them (a division by zero is all ones, a remainder by zero the dividend, a shift by
/// the width or more is 0 or the sign).
struct Lanes {
    w: u32,
    mask: u64,
}

impl Lanes {
    fn sx(&self, a: u64) -> i64 {
        let s = 64 - self.w;
        ((a << s) as i64) >> s
    }

    fn un(&self, op: UnOp, a: u64) -> u64 {
        match op {
            UnOp::Not => !a & self.mask,
            _ => a.wrapping_neg() & self.mask,
        }
    }

    fn cmp(&self, op: CmpOp, a: u64, b: u64) -> u64 {
        u64::from(match op {
            CmpOp::Eq => a == b,
            CmpOp::Ne => a != b,
            CmpOp::Ult => a < b,
            CmpOp::Ule => a <= b,
            CmpOp::Slt => self.sx(a) < self.sx(b),
            CmpOp::Sle => self.sx(a) <= self.sx(b),
        })
    }

    fn bin(&self, op: BinOp, a: u64, b: u64) -> u64 {
        let w = u64::from(self.w);
        let m = self.mask;
        match op {
            BinOp::Add => a.wrapping_add(b) & m,
            BinOp::Sub => a.wrapping_sub(b) & m,
            BinOp::Mul => a.wrapping_mul(b) & m,
            BinOp::And => a & b,
            BinOp::Or => a | b,
            BinOp::Xor => a ^ b,
            BinOp::Shl => {
                if b >= w {
                    0
                } else {
                    (a << b) & m
                }
            }
            BinOp::LShr => {
                if b >= w {
                    0
                } else {
                    a >> b
                }
            }
            BinOp::AShr => {
                let s = self.sx(a);
                (if b >= w { s >> 63 } else { s >> b }) as u64 & m
            }
            BinOp::UDiv => a.checked_div(b).unwrap_or(m),
            BinOp::URem => a.checked_rem(b).unwrap_or(a),
            _ => unreachable!("an operator of the grammar"),
        }
    }
}

/// The enumeration at one set of sample points.
struct Search<'a> {
    lanes: Lanes,
    points: &'a [Vec<u64>],
    terms: Vec<Term>,
    sizes: Vec<u8>,
    /// Each term's values at the points, `points.len()` words per term.
    values: Vec<u64>,
    seen: HashMap<u64, Vec<u32>>,
    by_size: Vec<Vec<u32>>,
}

enum Step {
    /// A candidate with the target's behavior was proved, or refuted (then the points
    /// change).
    Candidate,
    /// Not found within the limits.
    Exhausted,
}

fn hash(v: &[u64]) -> u64 {
    let mut h: u64 = 0xcbf2_9ce4_8422_2325;
    for &x in v {
        h ^= x;
        h = h.wrapping_mul(0x0000_0100_0000_01b3).rotate_left(17);
    }
    h
}

impl Search<'_> {
    fn n(&self) -> usize {
        self.points.len()
    }

    fn row(&self, t: u32) -> &[u64] {
        let n = self.n();
        &self.values[t as usize * n..(t as usize + 1) * n]
    }

    /// Adds a term with these values unless one with them exists: its index if new.
    fn add(&mut self, t: Term, size: u8, row: Vec<u64>) -> Option<u32> {
        let h = hash(&row);
        if let Some(list) = self.seen.get(&h)
            && list.iter().any(|&k| self.row(k) == &row[..])
        {
            return None;
        }
        let k = self.terms.len() as u32;
        self.terms.push(t);
        self.sizes.push(size);
        self.values.extend_from_slice(&row);
        self.seen.entry(h).or_default().push(k);
        self.by_size[size as usize].push(k);
        Some(k)
    }

    /// Enumerates by size until a term behaves like `target` (skipping the ones in `refuted`).
    /// Enumerates by size until a term behaves like `target` (skipping the ones in
    /// `refuted`); then, where none does, looks for two of the terms whose sum, difference
    /// or exclusive or does ([`pairs`](Self::pairs)).
    fn run(
        &mut self,
        leaves: &[Term],
        target: &[u64],
        max_size: u8,
        max_terms: usize,
        comparisons: bool,
        refuted: &mut dyn FnMut(u32, &Search<'_>) -> Result<bool, Error>,
    ) -> Result<Step, Error> {
        match self.enumerate(leaves, target, max_size, max_terms, comparisons, refuted)? {
            Step::Candidate => Ok(Step::Candidate),
            Step::Exhausted => self.pairs(target, refuted),
        }
    }

    /// Two enumerated terms that make the target together: `t + c`, `t − c`, `c − t` or
    /// `t ^ c`. For each term `t` the other is looked up by the values it must have, so an
    /// answer of twice the enumeration's size is found where its top is one of these: a sum
    /// with a correction (`x − 2 − zext(x == 0 | y == 0)`), a value with a flag in bits it
    /// has clear. The smallest pairs are tried first, at most [`MAX_PAIRS`] of them.
    fn pairs(
        &mut self,
        target: &[u64],
        refuted: &mut dyn FnMut(u32, &Search<'_>) -> Result<bool, Error>,
    ) -> Result<Step, Error> {
        let n = self.n();
        let count = self.terms.len() as u32;
        let mut found: Vec<(u8, Term)> = Vec::new();
        let mut row = vec![0u64; n];
        for t in 0..count {
            for op in [BinOp::Add, BinOp::Sub, BinOp::Xor] {
                // `c` with `t op c` the target; and for a difference, with `c − t` it too.
                for flip in [false, true] {
                    if flip && op != BinOp::Sub {
                        continue;
                    }
                    for (p, slot) in row.iter_mut().enumerate() {
                        let (tv, want) = (self.row(t)[p], target[p]);
                        *slot = match (op, flip) {
                            (BinOp::Add, _) => self.lanes.bin(BinOp::Sub, want, tv),
                            (BinOp::Sub, false) => self.lanes.bin(BinOp::Sub, tv, want),
                            (BinOp::Sub, true) => self.lanes.bin(BinOp::Add, want, tv),
                            _ => want ^ tv,
                        };
                    }
                    let Some(list) = self.seen.get(&hash(&row)) else {
                        continue;
                    };
                    let Some(&c) = list.iter().find(|&&k| self.row(k) == &row[..]) else {
                        continue;
                    };
                    // (A commutative pair once.)
                    if op != BinOp::Sub && c < t {
                        continue;
                    }
                    let size = self.sizes[t as usize]
                        .saturating_add(self.sizes[c as usize])
                        .saturating_add(1);
                    let term = if flip {
                        Term::Bin(op, c, t)
                    } else {
                        Term::Bin(op, t, c)
                    };
                    found.push((size, term));
                }
            }
        }
        found.sort_by_key(|f| f.0);
        for (size, term) in found.into_iter().take(MAX_PAIRS) {
            // (Not among the terms of the enumeration: nothing is built over it.)
            let k = self.terms.len() as u32;
            self.terms.push(term);
            self.sizes.push(size);
            self.values.extend_from_slice(target);
            if !refuted(k, self)? {
                return Ok(Step::Candidate);
            }
        }
        Ok(Step::Exhausted)
    }

    fn enumerate(
        &mut self,
        leaves: &[Term],
        target: &[u64],
        max_size: u8,
        max_terms: usize,
        comparisons: bool,
        refuted: &mut dyn FnMut(u32, &Search<'_>) -> Result<bool, Error>,
    ) -> Result<Step, Error> {
        let n = self.n();
        self.by_size = vec![Vec::new(); max_size as usize + 1];
        for &l in leaves {
            let row: Vec<u64> = (0..n)
                .map(|p| match l {
                    Term::Var(v) => self.points[p][v],
                    Term::Const(c) => c,
                    _ => unreachable!("a leaf"),
                })
                .collect();
            let is_target = row[..] == target[..];
            if let Some(k) = self.add(l, 1, row)
                && is_target
                && !refuted(k, self)?
            {
                return Ok(Step::Candidate);
            }
        }
        for size in 2..=max_size {
            // Unary: one operand of size − 1.
            let prev: Vec<u32> = self.by_size[size as usize - 1].clone();
            for op in UNARY {
                for &a in &prev {
                    let row: Vec<u64> = self.row(a).iter().map(|&x| self.lanes.un(op, x)).collect();
                    let is_target = row[..] == target[..];
                    if let Some(k) = self.add(Term::Un(op, a), size, row)
                        && is_target
                        && !refuted(k, self)?
                    {
                        return Ok(Step::Candidate);
                    }
                    if self.terms.len() >= max_terms {
                        return Ok(Step::Exhausted);
                    }
                }
            }
            // Binary: operands of sizes i and size − 1 − i.
            for i in 1..size - 1 {
                let j = size - 1 - i;
                let left: Vec<u32> = self.by_size[i as usize].clone();
                let right: Vec<u32> = self.by_size[j as usize].clone();
                for op in BINARY {
                    if commutative(op) && i > j {
                        continue;
                    }
                    for &a in &left {
                        for &b in &right {
                            if commutative(op) && i == j && b < a {
                                continue;
                            }
                            let ra = self.row(a);
                            let rb = self.row(b);
                            let row: Vec<u64> = ra
                                .iter()
                                .zip(rb)
                                .map(|(&x, &y)| self.lanes.bin(op, x, y))
                                .collect();
                            let is_target = row[..] == target[..];
                            if let Some(k) = self.add(Term::Bin(op, a, b), size, row)
                                && is_target
                                && !refuted(k, self)?
                            {
                                return Ok(Step::Candidate);
                            }
                            if self.terms.len() >= max_terms {
                                return Ok(Step::Exhausted);
                            }
                        }
                    }
                }
                if !comparisons {
                    continue;
                }
                for op in COMPARE {
                    let symmetric = matches!(op, CmpOp::Eq | CmpOp::Ne);
                    if symmetric && i > j {
                        continue;
                    }
                    for &a in &left {
                        for &b in &right {
                            if symmetric && i == j && b < a {
                                continue;
                            }
                            let ra = self.row(a);
                            let rb = self.row(b);
                            let row: Vec<u64> = ra
                                .iter()
                                .zip(rb)
                                .map(|(&x, &y)| self.lanes.cmp(op, x, y))
                                .collect();
                            let is_target = row[..] == target[..];
                            if let Some(k) = self.add(Term::Cmp(op, a, b), size, row)
                                && is_target
                                && !refuted(k, self)?
                            {
                                return Ok(Step::Candidate);
                            }
                            if self.terms.len() >= max_terms {
                                return Ok(Step::Exhausted);
                            }
                        }
                    }
                }
            }
        }
        Ok(Step::Exhausted)
    }

    /// Term `k` as an expression.
    fn build(&self, cx: &mut Context, vars: &[Expr], width: Width, k: u32) -> Result<Expr, Error> {
        Ok(match self.terms[k as usize] {
            Term::Var(v) => vars[v],
            Term::Const(c) => cx.constant(&BitVec::wrapping_from_u64(width, c))?,
            Term::Un(op, a) => {
                let a = self.build(cx, vars, width, a)?;
                cx.un(op, a)?
            }
            Term::Bin(op, a, b) => {
                let (a, b) = (
                    self.build(cx, vars, width, a)?,
                    self.build(cx, vars, width, b)?,
                );
                cx.bin(op, a, b)?
            }
            Term::Cmp(op, a, b) => {
                let (a, b) = (
                    self.build(cx, vars, width, a)?,
                    self.build(cx, vars, width, b)?,
                );
                let c = cx.cmp(op, a, b)?;
                cx.zext(c, width)?
            }
        })
    }
}

/// The constants `e` mentions (at its width), besides 0, 1 and all ones; then the ones its
/// slices and extensions imply: bits `[lo, lo + n)` of a value of the target's width are
/// `(x >>u lo) & (2^n − 1)`, and `x & mask` in place, so the count and both masks are
/// candidates' constants (`zext<64>(trunc<8>(x))` is `x & 255`, which mentions no 255).
fn constants(cx: &mut Context, e: Expr, w: Width) -> Result<Vec<u64>, Error> {
    let mut out = Vec::new();
    let mut implied = Vec::new();
    let bits = w.bits();
    for x in cx.post_order(&[e])? {
        let xw = cx.width(x)?;
        match cx.view(x)? {
            View::Const(c) if xw == w => {
                if let Some(v) = c.to_u64()
                    && !out.contains(&v)
                {
                    out.push(v);
                }
            }
            View::Extract { lo, src } if cx.width(src)? == w && xw.bits() < 64 => {
                let low = (1u64 << xw.bits()) - 1;
                implied.extend([low, low << lo, u64::from(lo)]);
            }
            View::Zext(a) | View::Sext(a) if xw == w => {
                let n = cx.width(a)?.bits();
                if n > 1 && n < bits {
                    implied.push((1u64 << n) - 1);
                }
            }
            _ => {}
        }
    }
    for v in implied {
        if v != 0 && !out.contains(&v) {
            out.push(v);
        }
    }
    Ok(out)
}

/// What a search found, and what it could not settle.
#[derive(Clone, Debug, Default)]
#[non_exhaustive]
pub struct Report {
    /// A smaller expression equal to the target (proved), if one was found.
    pub found: Option<Expr>,
    /// The candidate that behaves like the target at every sample point but whose proof was
    /// not decided, with why: one left by [`prove::Unknown::Budget`] may be proved with a
    /// larger [`Config::conflicts`] or [`Config::propagations`]. (At most one: no other term
    /// behaves like it at the points, so the search ends there.)
    pub unproved: Option<(Expr, prove::Unknown)>,
}

/// A smaller expression equal to `e` (proved), over `e`'s variables, the constants it mentions,
/// 0, 1, all ones, the width less one and the sign bit, and the operators `~ − + − · & | ^ << >>u >>s udiv urem`; `None` when
/// none is found within the limits. Only for a value of at most 64 bits whose variables all
/// have its width. [`synthesize_report`] also says which candidate was left unproved.
pub fn synthesize(cx: &mut Context, e: Expr, cfg: &Config) -> Result<Option<Expr>, Error> {
    Ok(synthesize_report(cx, e, cfg)?.found)
}

/// [`synthesize`], with the candidate whose proof was not decided ([`Report::unproved`]).
pub fn synthesize_report(cx: &mut Context, e: Expr, cfg: &Config) -> Result<Report, Error> {
    let nothing = Ok(Report::default());
    let width = cx.width(e)?;
    let w = u32::from(width.bits());
    if w > 64 {
        return nothing;
    }
    let mask = if w == 64 { u64::MAX } else { (1u64 << w) - 1 };
    let ids = cx.symbols_in(&[e])?;
    let mut vars = Vec::with_capacity(ids.len());
    let mut keys: Vec<SymbolKey> = Vec::new();
    for id in ids {
        let (Some(k), Some(sw)) = (cx.symbol_key(id).cloned(), cx.symbol_width(id)) else {
            continue;
        };
        if sw != width {
            return nothing;
        }
        vars.push(cx.symbol(k.clone(), sw)?);
        keys.push(k);
    }
    if vars.len() > cfg.max_vars {
        return nothing;
    }
    // Candidates are enumerated by tree size, up to the target's less one; an answer must also
    // be smaller as a DAG (what it costs).
    let limit = (cx.tree_size(e)?.saturating_sub(1)).min(u32::from(cfg.max_size)) as u8;
    let dag = match cx.dag_size(&[e], u32::MAX)? {
        crate::Bounded::Exact(n) | crate::Bounded::AtLeast(n) => n,
    };
    if limit == 0 {
        return nothing;
    }
    let mut leaves: Vec<Term> = (0..vars.len()).map(Term::Var).collect();
    let mut consts = vec![
        0,
        1 & mask,
        mask,
        u64::from(w - 1) & mask,
        (1u64 << (w - 1)) & mask,
    ];
    for c in constants(cx, e, width)? {
        if !consts.contains(&c) {
            consts.push(c);
        }
    }
    consts.dedup();
    consts.truncate(10);
    leaves.extend(consts.iter().map(|&c| Term::Const(c)));
    // Sample points: boundary values, then pseudo-random ones.
    let nv = vars.len();
    let mut points: Vec<Vec<u64>> = Vec::new();
    let specials = [
        0,
        1 & mask,
        mask,
        (1u64 << (w - 1)) & mask,
        mask >> 1,
        2 & mask,
    ];
    for s in 0..specials.len() {
        points.push(
            (0..nv)
                .map(|v| specials[(s + v) % specials.len()])
                .collect(),
        );
    }
    let mut state = 0x2545_f491_4f6c_dd1du64 ^ u64::from(w);
    let mut next = || {
        state ^= state << 13;
        state ^= state >> 7;
        state ^= state << 17;
        state
    };
    for _ in 0..cfg.samples {
        points.push((0..nv).map(|_| next() & mask).collect());
    }
    let pcfg = prove::Config::default()
        .with_max_conflicts(cfg.conflicts)
        .with_max_propagations(cfg.propagations);
    for _restart in 0..=cfg.restarts {
        // The target's behavior at the points.
        let mut target = Vec::with_capacity(points.len());
        for p in &points {
            target.push(value_at(cx, e, &keys, width, p)?);
        }
        let mut s = Search {
            lanes: Lanes { w, mask },
            points: &points,
            terms: Vec::new(),
            sizes: Vec::new(),
            values: Vec::new(),
            seen: HashMap::new(),
            by_size: Vec::new(),
        };
        let mut counterexample: Option<Vec<u64>> = None;
        let mut found: Option<Expr> = None;
        let mut unproved: Option<(Expr, prove::Unknown)> = None;
        let step = {
            let mut check = |k: u32, s: &Search<'_>| -> Result<bool, Error> {
                // `true`: refuted (keep searching).
                let cand = s.build(cx, &vars, width, k)?;
                let smaller = match cx.dag_size(&[cand], dag)? {
                    crate::Bounded::Exact(n) => n < dag,
                    crate::Bounded::AtLeast(_) => false,
                };
                if cand == e || !smaller {
                    return Ok(true);
                }
                match prove::equal(cx, e, cand, &pcfg)? {
                    Outcome::Proved(_) => {
                        found = Some(cand);
                        Ok(false)
                    }
                    Outcome::Refuted(model) => {
                        let p: Vec<u64> = keys
                            .iter()
                            .map(|k| {
                                model
                                    .iter()
                                    .find(|(kk, _)| kk == k)
                                    .and_then(|(_, v)| v.to_u64())
                                    .unwrap_or(0)
                            })
                            .collect();
                        counterexample = Some(p);
                        // Stop: the points change and the search starts over.
                        Ok(false)
                    }
                    Outcome::Unknown(why) => {
                        // (The first is the smallest.)
                        unproved.get_or_insert((cand, why));
                        Ok(true)
                    }
                }
            };
            s.run(
                &leaves,
                &target,
                limit,
                cfg.max_terms,
                cfg.comparisons,
                &mut check,
            )?
        };
        if let Some(f) = found {
            return Ok(Report {
                found: Some(f),
                unproved: None,
            });
        }
        match (step, counterexample) {
            (_, Some(p)) => points.push(p),
            (Step::Exhausted | Step::Candidate, None) => {
                return Ok(Report {
                    found: None,
                    unproved,
                });
            }
        }
    }
    // Out of restarts: every round ended with a counterexample.
    nothing
}

/// `x`'s value at `p`, a value for each symbol of `keys`.
fn value_at(
    cx: &mut Context,
    x: Expr,
    keys: &[SymbolKey],
    width: Width,
    p: &[u64],
) -> Result<u64, Error> {
    let env: Vec<(SymbolKey, BitVec)> = keys
        .iter()
        .zip(p)
        .map(|(k, &v)| (k.clone(), BitVec::wrapping_from_u64(width, v)))
        .collect();
    Ok(cx.eval(&[x], &env[..])?[0].to_u64().unwrap_or(0))
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::ParseOptions;

    fn synth(text: &str, w: Width) -> Option<String> {
        let mut cx = Context::new();
        let e = cx.parse(text, &ParseOptions::width(w)).unwrap();
        synthesize(&mut cx, e, &Config::default())
            .unwrap()
            .map(|s| cx.display(s).to_string())
    }

    #[test]
    fn smaller_equivalents() {
        assert_eq!(
            synth("(x ^ y) + 2 * (x & y)", Width::W32).as_deref(),
            Some("x + y")
        );
        assert_eq!(
            synth("(x | y) + (x & y) - x", Width::W64).as_deref(),
            Some("y")
        );
        // Not an MBA: shifts and a division.
        assert_eq!(
            synth("((x >>u 3) << 3) | (x & 7)", Width::W16).as_deref(),
            Some("x")
        );
        assert_eq!(
            synth("udiv(x << 2, 4) << 2", Width::W8).as_deref(),
            Some("x * 4")
        );
        // Already minimal.
        assert_eq!(synth("x + y", Width::W32), None);
    }

    /// Comparisons are candidates: a value's being zero spelled in arithmetic is the
    /// comparison, and a correction where two values meet is written with one.
    #[test]
    fn comparisons_are_candidates() {
        for (src, want) in [
            ("(x | -x) >>u 63", "zext<64>(x != 0)"),
            ("((x ^ y) | -(x ^ y)) >>u 63", "zext<64>(x != y)"),
            (
                "((~x & y) | ((~x | y) & (x - y))) >>u 63",
                "zext<64>(x <u y)",
            ),
            (
                "((x - y) ^ ((x ^ y) & ((x - y) ^ x))) >>u 63",
                "zext<64>(x <s y)",
            ),
        ] {
            assert_eq!(synth(src, Width::W64).as_deref(), Some(want), "{src}");
        }
        // Without them, no comparison.
        let mut cx = Context::new();
        let e = cx
            .parse("(x | -x) >>u 63", &ParseOptions::width(Width::W64))
            .unwrap();
        let cfg = Config::default().with_comparisons(false);
        let out = synthesize(&mut cx, e, &cfg).unwrap();
        let text = out.map(|o| cx.display(o).to_string()).unwrap_or_default();
        assert!(!text.contains("!=") && !text.contains("=="), "{text}");
    }

    /// A sum with a correction where a value is zero, and a value with a flag in bits it has
    /// clear, under noise the engine leaves: each is two terms of the enumeration joined, of
    /// more nodes together than the enumeration reaches.
    #[test]
    fn two_terms_make_an_answer_beyond_the_enumeration() {
        for (src, want) in [
            (
                "x1 - 2 - zext<64>((x0 == 0) | (x1 == 0))",
                "x1 - zext<64>(x0 << x1 == x0) - 2",
            ),
            (
                "(x & 0xffffff00) | zext<64>((x & ~1) == 2)",
                "(x & 0xffffff00) + zext<64>(x >>u 1 == 1)",
            ),
        ] {
            let noisy = format!("(({src}) ^ (y & ~y)) + (y - y)");
            assert_eq!(synth(&noisy, Width::W64).as_deref(), Some(want), "{src}");
        }
    }

    /// A slice extended back is a mask, whose constant the target does not mention.
    #[test]
    fn a_slice_is_its_mask() {
        for (src, want) in [
            ("zext<64>(trunc<8>(x:64 ^ y) ^ trunc<8>(y))", "x & 255"),
            (
                "zext<64>(trunc<8>(x:64)) + zext<64>(trunc<8>(~x))",
                "255:64",
            ),
            (
                "zext<64>(extract<8, 8>(x:64 ^ y) ^ extract<8, 8>(y)) << 8",
                "x & 65280",
            ),
        ] {
            assert_eq!(synth(src, Width::W64).as_deref(), Some(want), "{src}");
        }
    }

    #[test]
    fn a_rare_difference_is_found_and_nothing_wrong_is_returned() {
        // Equal to x except at one input, which sampling misses: the prover's counterexample
        // restarts the search, and nothing smaller is equal; no proof was left undecided.
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let e = cx.parse("select(x == 0x12345678, 1, x)", &o).unwrap();
        let r = synthesize_report(&mut cx, e, &Config::default()).unwrap();
        assert!(r.found.is_none() && r.unproved.is_none(), "{r:?}");
    }

    #[test]
    fn a_proof_past_the_budget_leaves_its_candidate_unproved() {
        // 0, by a product's factor shifted either way: the proof takes SAT work.
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let e = cx.parse("((x << z) * y) ^ ((x * y) << z)", &o).unwrap();
        let zero = cx.zero(Width::W8).unwrap();
        let r = synthesize_report(&mut cx, e, &Config::default()).unwrap();
        assert_eq!(r.found, Some(zero));
        for cfg in [
            Config::default().with_conflicts(1),
            Config::default().with_propagations(100),
        ] {
            let r = synthesize_report(&mut cx, e, &cfg).unwrap();
            assert_eq!(r.found, None);
            let Some((c, why)) = r.unproved else {
                panic!("{r:?}")
            };
            assert!(c == zero && why.is_budget(), "{why}");
        }
    }
}
