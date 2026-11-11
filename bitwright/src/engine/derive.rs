//! A simplification as a derivation: its steps, written so that they can be checked apart
//! from the engine that made them.

use core::ops::Range;

use super::{By, Engine, Event, Observer, RootOutcome, Run};
#[cfg(feature = "prove")]
use crate::Width;
use crate::error::Error;
use crate::expr::{Context, Expr};
#[cfg(feature = "prove")]
use crate::text::ParseOptions;
use crate::text::PrintOptions;

/// One rewrite of a derivation: what made it, and the subexpression before and after, as
/// text that parses in any context (symbols with their widths).
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Rewritten {
    /// The rule (`group::rule`), the pass, or the whole-root stage that made it.
    pub by: String,
    /// The width of both sides.
    pub width: u16,
    /// The subexpression rewritten.
    pub before: String,
    /// What it became.
    pub after: String,
}

/// A phase of the strategy (or a stage outside the phases) that changed the expression: what
/// it began on, what it left, and which of the derivation's steps it made.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Stretch {
    /// The phase's name ([`Phase::name`](super::Phase::name)) or the stage's.
    pub by: String,
    /// The whole expression when it began.
    pub from: String,
    /// The whole expression when it ended.
    pub to: String,
    /// Its steps, as positions in [`Derivation::steps`].
    pub steps: Range<usize>,
}

/// How an engine got from an expression to its result: every rewrite it reported, in order,
/// and the expression at each phase's beginning and end.
///
/// A derivation claims that each step's two sides are equal, and that each phase's steps
/// lead from what it began on to what it left. Neither claim needs the engine to check:
/// [`check`](Self::check) has each step proved by the circuit and the search alone and
/// replays each phase in a context of its own, and [`lean`](Self::lean) writes the steps as
/// Lean theorems. A step is small where the whole is not, which is what makes a word-level
/// result something another prover can follow.
///
/// Not every pass reports what it did as steps that replay. Some rewrite a subexpression
/// into one equal only on the bits its users read, or report a rewrite of something they
/// built on the way; a phase whose steps do not lead to what it left is one the derivation
/// does not explain, and `check` says which those are.
///
/// ```
/// use bitwright::engine::{Engine, Run};
/// use bitwright::{Context, ParseOptions, Width};
///
/// let mut cx = Context::new();
/// let e = cx.parse("((x & y) + (x | y)) * 3 + (z ^ z)", &ParseOptions::width(Width::W32))?;
/// let (out, derivation) = Engine::standard().derive(&mut cx, e, Run::default())?;
/// assert_eq!(cx.display(out.expr).to_string(), "(x + y) * 3");
/// assert_eq!(derivation.to, "(x:32 + y:32) * 3");
/// assert!(!derivation.steps.is_empty());
/// # #[cfg(feature = "prove")]
/// # {
/// let report = derivation.check(&bitwright::prove::Config::default())?;
/// assert!(report.certified() && report.unproved.is_empty());
/// # }
/// # Ok::<(), bitwright::Error>(())
/// ```
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct Derivation {
    /// The width of the expression.
    pub width: u16,
    /// The expression given.
    pub from: String,
    /// The result.
    pub to: String,
    /// The rewrites, in the order they were made.
    pub steps: Vec<Rewritten>,
    /// The phases and stages that changed the expression, in order: each begins on what
    /// the one before it left.
    pub stretches: Vec<Stretch>,
}

/// Collects the rewrites of a run and the roots at its phases' ends.
#[derive(Default)]
struct Collector {
    steps: Vec<(String, Expr, Expr)>,
    /// Per phase or stage that changed the root: its name, the roots, its steps.
    stretches: Vec<(String, Expr, Expr, Range<usize>)>,
    /// The phase in progress: its root and where its steps begin.
    open: Option<(Expr, usize)>,
    /// Where the parts of the stage in progress begin, when it reported any.
    parts: Option<usize>,
    /// The strategy's phase names.
    names: Vec<&'static str>,
}

impl Observer for Collector {
    fn event(&mut self, event: Event<'_>) {
        match event {
            Event::Applied { by, before, after } => {
                let name = match by {
                    By::Rule(r) => r.name.clone(),
                    other => other.name().to_string(),
                };
                self.steps.push((name, before, after));
            }
            // An application a postcondition or the host turned down was not made.
            Event::Rejected { .. } | Event::Vetoed { .. } => {
                if self.open.is_some_and(|(_, start)| self.steps.len() > start) {
                    self.steps.pop();
                }
            }
            // What a stage found of parts of the root: the steps its rewrite is made of.
            Event::Part {
                stage,
                before,
                after,
            } => {
                if self.parts.is_none() {
                    self.parts = Some(self.steps.len());
                }
                self.steps.push((stage.name().to_string(), before, after));
            }
            Event::Stage {
                stage,
                before,
                after,
            } => {
                // By its parts, where it said them; else as the one step it is.
                let at = match self.parts.take() {
                    Some(at) => at,
                    None => {
                        self.steps.push((stage.name().to_string(), before, after));
                        self.steps.len() - 1
                    }
                };
                let steps = at..self.steps.len();
                (self.stretches).push((stage.name().to_string(), before, after, steps));
            }
            Event::PhaseBegin { root, .. } => self.open = Some((root, self.steps.len())),
            Event::PhaseEnd { phase, root, .. } => {
                if let Some((from, start)) = self.open.take()
                    && from != root
                {
                    let name = self.names.get(phase).copied().unwrap_or("phase");
                    (self.stretches).push((name.to_string(), from, root, start..self.steps.len()));
                }
            }
            _ => {}
        }
    }
}

fn text(cx: &Context, e: Expr) -> String {
    let opts = PrintOptions::default()
        .with_symbol_widths(true)
        .with_max_nodes(usize::MAX)
        .with_max_chars(usize::MAX);
    cx.display_with(e, opts).to_string()
}

impl Engine {
    /// Simplifies `e` as [`run`](Self::run) does, and returns the steps taken with the
    /// result. The run is made afresh (what the context remembers of `e` is set aside for
    /// it, so that every step is seen) and without assumptions or an observer of the
    /// caller's: `run`'s are ignored.
    pub fn derive(
        &self,
        cx: &mut Context,
        e: Expr,
        run: Run<'_>,
    ) -> Result<(RootOutcome, Derivation), Error> {
        let mut seen = Collector {
            names: self.strategy().phases.iter().map(|p| p.name()).collect(),
            ..Collector::default()
        };
        let run = Run {
            observer: Some(&mut seen),
            assumptions: None,
            allowance: run.allowance,
            per_call: run.per_call,
            admission: run.admission,
            hooks: run.hooks,
            deadline: run.deadline,
        };
        let kept = core::mem::take(&mut cx.memo);
        let out = self.run(cx, &[e], run);
        cx.memo = kept;
        let out = out?.roots[0];
        let mut steps = Vec::with_capacity(seen.steps.len());
        for (by, before, after) in seen.steps {
            steps.push(Rewritten {
                by,
                width: cx.width(before)?.bits(),
                before: text(cx, before),
                after: text(cx, after),
            });
        }
        let stretches = (seen.stretches.into_iter())
            .map(|(by, from, to, steps)| Stretch {
                by,
                from: text(cx, from),
                to: text(cx, to),
                steps,
            })
            .collect();
        let derivation = Derivation {
            width: cx.width(e)?.bits(),
            from: text(cx, e),
            to: text(cx, out.expr),
            steps,
            stretches,
        };
        Ok((out, derivation))
    }
}

/// The most monomials a polynomial may have in [`ring_equal`].
#[cfg(any(feature = "prove", feature = "mba"))]
const RING_TERMS: usize = 4096;

/// A polynomial modulo `2^w` (`w` at most 64) over atoms (nodes that are not sums, products,
/// negations, complements or shifts left by a constant): its monomials, each the sorted
/// atoms it multiplies, with their coefficients.
#[cfg(any(feature = "prove", feature = "mba"))]
type Poly = std::collections::BTreeMap<Vec<u32>, u64>;

#[cfg(any(feature = "prove", feature = "mba"))]
fn poly_add(p: &mut Poly, q: &Poly, sign: u64, mask: u64) {
    for (m, &c) in q {
        let e = p.entry(m.clone()).or_insert(0);
        *e = e.wrapping_add(c.wrapping_mul(sign)) & mask;
    }
    p.retain(|_, c| *c != 0);
}
/// The polynomial of `e` modulo `mask + 1`, or `None` past [`RING_TERMS`].
#[cfg(any(feature = "prove", feature = "mba"))]
fn poly(
    cx: &Context,
    e: Expr,
    mask: u64,
    memo: &mut std::collections::HashMap<Expr, Option<Poly>>,
) -> Result<Option<Poly>, Error> {
    use crate::View;
    use crate::ops::{BinOp, UnOp};
    if let Some(p) = memo.get(&e) {
        return Ok(p.clone());
    }
    let atom = || Some(Poly::from([(vec![e.index()], 1)]));
    let p = match cx.view(e)? {
        View::Const(v) => v.to_u64().map(|c| {
            let mut p = Poly::new();
            if c & mask != 0 {
                p.insert(Vec::new(), c & mask);
            }
            p
        }),
        View::Bin(op @ (BinOp::Add | BinOp::Sub), x, y) => {
            match (poly(cx, x, mask, memo)?, poly(cx, y, mask, memo)?) {
                (Some(mut p), Some(q)) => {
                    poly_add(
                        &mut p,
                        &q,
                        if op == BinOp::Add { 1 } else { u64::MAX },
                        mask,
                    );
                    Some(p)
                }
                _ => None,
            }
        }
        View::Bin(BinOp::Mul, x, y) => match (poly(cx, x, mask, memo)?, poly(cx, y, mask, memo)?) {
            (Some(p), Some(q)) if p.len().saturating_mul(q.len()) <= RING_TERMS => {
                let mut r = Poly::new();
                for (m, &c) in &p {
                    for (n, &d) in &q {
                        let mut mn = [m.as_slice(), n.as_slice()].concat();
                        mn.sort_unstable();
                        let e = r.entry(mn).or_insert(0);
                        *e = e.wrapping_add(c.wrapping_mul(d)) & mask;
                    }
                }
                r.retain(|_, c| *c != 0);
                Some(r)
            }
            (Some(_), Some(_)) => None,
            _ => None,
        },
        View::Bin(BinOp::Shl, x, k) => match (cx.as_const(k)?.and_then(|v| v.to_u64()), x) {
            (Some(k), x) if k < 64 => poly(cx, x, mask, memo)?.map(|p| {
                let mut r = Poly::new();
                poly_add(&mut r, &p, 1u64 << k, mask);
                r
            }),
            (Some(_), _) => Some(Poly::new()),
            (None, _) => atom(),
        },
        View::Un(UnOp::Neg, x) => poly(cx, x, mask, memo)?.map(|p| {
            let mut r = Poly::new();
            poly_add(&mut r, &p, u64::MAX, mask);
            r
        }),
        // `~x` is `-x - 1`.
        View::Un(UnOp::Not, x) => poly(cx, x, mask, memo)?.map(|p| {
            let mut r = Poly::from([(Vec::new(), mask)]);
            poly_add(&mut r, &p, u64::MAX, mask);
            r
        }),
        _ => atom(),
    };
    let p = p.filter(|p| p.len() <= RING_TERMS);
    memo.insert(e, p.clone());
    Ok(p)
}

/// Whether `a` and `b` are the same polynomial modulo `2^w` over their atoms, which makes
/// them equal at every value: the ring laws and nothing else. `false` decides nothing (the
/// width is over 64 bits, a polynomial grew past [`RING_TERMS`], or they differ as
/// polynomials while equal as functions).
#[cfg(feature = "prove")]
pub(super) fn ring_equal(cx: &Context, a: Expr, b: Expr) -> Result<bool, Error> {
    let w = cx.width(a)?.bits();
    if w > 64 || cx.width(b)?.bits() != w {
        return Ok(false);
    }
    let mask = u64::MAX >> (64 - u32::from(w));
    let mut memo = std::collections::HashMap::new();
    Ok(
        match (poly(cx, a, mask, &mut memo)?, poly(cx, b, mask, &mut memo)?) {
            (Some(p), Some(q)) => p == q,
            _ => false,
        },
    )
}

/// The most atoms of a linear MBA whose corners are enumerated (`2^t` evaluations).
#[cfg(any(feature = "prove", feature = "mba"))]
const CORNER_ATOMS: usize = 12;

/// The most evaluations of a node spent on one question where the bitwise functions have
/// constants inside (`width * 2^t` points, each all the nodes).
#[cfg(any(feature = "prove", feature = "mba"))]
const CORNER_WORK: usize = 20_000_000;

/// Whether `a` and `b` are equal because both are linear MBAs over the same atoms and agree
/// at every corner: each a sum of constant multiples of bitwise functions (`&`, `|`, `^`,
/// `~` over atoms and constants). `false` decides nothing.
///
/// Bit `i` of a bitwise function reads bit `i` of each atom and nothing else, so the
/// difference of the two sides is a sum over the bit positions of a function of the atoms'
/// bits there. With no constant inside but 0 and all ones that function is the same at every
/// position, and the difference is zero everywhere when it is zero where every atom is all
/// zeros or all ones. With constants (masks) it differs by position, and the difference is
/// zero everywhere when it is zero at all zeros and wherever the atoms are zero but at one
/// position.
#[cfg(feature = "prove")]
pub(super) fn corners_equal(cx: &Context, a: Expr, b: Expr) -> Result<bool, Error> {
    corners_equal_given(cx, a, b, &[])
}

/// [`corners_equal`] where each of `zeros` is zero: bitwise functions of the atoms that are
/// known to vanish (two atoms with no bit in common: their conjunction). A corner at which
/// one of them is not zero is a value the atoms never have at any bit, and is not asked
/// about. (Facts that are not bitwise functions of the atoms, or any fact where a mask is
/// involved, are not used: the answer is then for every value.)
#[cfg(any(feature = "prove", feature = "mba"))]
pub(crate) fn corners_equal_given(
    cx: &Context,
    a: Expr,
    b: Expr,
    zeros: &[Expr],
) -> Result<bool, Error> {
    use crate::View;
    use crate::ops::{BinOp, UnOp};
    let w = cx.width(a)?.bits();
    if w > 64 || cx.width(b)?.bits() != w {
        return Ok(false);
    }
    let mask = u64::MAX >> (64 - u32::from(w));
    /// What a node is in a linear MBA.
    #[derive(Copy, Clone, PartialEq)]
    enum Kind {
        /// A bitwise function of atoms (an atom is one).
        Bitwise,
        /// A sum of constant multiples of bitwise functions.
        Linear,
    }
    struct Shape<'c> {
        cx: &'c Context,
        w: u16,
        mask: u64,
        /// The atoms, each with its polynomial.
        atoms: Vec<(Expr, Option<Poly>)>,
        /// The nodes read as an atom or (`true`) as the complement of one: the atoms
        /// themselves, and the sums that are another atom's value or its complement by the
        /// ring laws (`c - x` beside `x + (-1 - c)`).
        atom_of: std::collections::HashMap<Expr, (usize, bool)>,
        polys: std::collections::HashMap<Expr, Option<Poly>>,
        /// Whether a bitwise function has a constant other than 0 and all ones inside.
        masked: bool,
        kinds: std::collections::HashMap<Expr, Option<Kind>>,
    }
    impl Shape<'_> {
        /// The node's kind, or `None` when it is no linear MBA; atoms are collected.
        fn kind(&mut self, e: Expr) -> Result<Option<Kind>, Error> {
            if let Some(&k) = self.kinds.get(&e) {
                return Ok(k);
            }
            let k = match self.cx.view(e)? {
                // A constant is a bitwise function of no atom, and a linear term.
                View::Const(_) => Some(Kind::Bitwise),
                View::Bin(BinOp::And | BinOp::Or | BinOp::Xor, x, y) => {
                    match (self.kind(x)?, self.kind(y)?) {
                        (Some(kx), Some(ky)) => {
                            // A sum under a bitwise operation is an atom there.
                            let mut ok = true;
                            for (c, k) in [(x, kx), (y, ky)] {
                                if k == Kind::Linear {
                                    ok &= self.atom(c)?.is_some();
                                } else if let Some(v) = self.cx.as_const(c)? {
                                    self.masked |= !(v.is_zero() || v.is_ones());
                                }
                            }
                            ok.then_some(Kind::Bitwise)
                        }
                        _ => None,
                    }
                }
                View::Un(UnOp::Not, x) => self.kind(x)?,
                View::Un(UnOp::Neg, x) => self.kind(x)?.map(|_| Kind::Linear),
                View::Bin(BinOp::Add | BinOp::Sub, x, y) => match (self.kind(x)?, self.kind(y)?) {
                    (Some(_), Some(_)) => Some(Kind::Linear),
                    _ => None,
                },
                View::Bin(BinOp::Mul, x, y) => {
                    let constant = |s: &Self, e| Ok::<_, Error>(s.cx.as_const(e)?.is_some());
                    if constant(self, x)? || constant(self, y)? {
                        let other = if constant(self, x)? { y } else { x };
                        self.kind(other)?.map(|_| Kind::Linear)
                    } else {
                        self.atom(e)?
                    }
                }
                View::Bin(BinOp::Shl, x, k) if self.cx.as_const(k)?.is_some() => {
                    self.kind(x)?.map(|_| Kind::Linear)
                }
                _ => self.atom(e)?,
            };
            self.kinds.insert(e, k);
            Ok(k)
        }

        fn atom(&mut self, e: Expr) -> Result<Option<Kind>, Error> {
            if self.cx.width(e)?.bits() != self.w {
                return Ok(None);
            }
            if self.atom_of.contains_key(&e) {
                return Ok(Some(Kind::Bitwise));
            }
            let p = poly(self.cx, e, self.mask, &mut self.polys)?;
            // The same value as an atom, or its complement (`p + q == -1`).
            let mut found = None;
            if let Some(p) = &p {
                for (j, (_, q)) in self.atoms.iter().enumerate() {
                    let Some(q) = q else { continue };
                    if p == q {
                        found = Some((j, false));
                        break;
                    }
                    let mut sum = p.clone();
                    poly_add(&mut sum, q, 1, self.mask);
                    if sum.len() == 1 && sum.get(&Vec::new()) == Some(&self.mask) {
                        found = Some((j, true));
                        break;
                    }
                }
            }
            let at = match found {
                Some(at) => at,
                None => {
                    self.atoms.push((e, p));
                    (self.atoms.len() - 1, false)
                }
            };
            self.atom_of.insert(e, at);
            Ok((self.atoms.len() <= CORNER_ATOMS).then_some(Kind::Bitwise))
        }

        /// The nodes under `roots` down to the atoms, operands first.
        fn order(&self, roots: &[Expr]) -> Result<Vec<Expr>, Error> {
            let mut out = Vec::new();
            let mut seen = std::collections::HashSet::new();
            let mut stack: Vec<(Expr, bool)> = roots.iter().map(|&r| (r, false)).collect();
            while let Some((e, ready)) = stack.pop() {
                if ready {
                    out.push(e);
                } else if seen.insert(e) {
                    stack.push((e, true));
                    if !self.atom_of.contains_key(&e) {
                        stack.extend(self.cx.children(e)?.map(|c| (c, false)));
                    }
                }
            }
            Ok(out)
        }

        /// The values of `order`'s nodes where atom `j` is `ones` when bit `j` of `corner`
        /// is set and zero otherwise, into `at`.
        fn values(
            &self,
            order: &[Expr],
            corner: usize,
            ones: u64,
            mask: u64,
            at: &mut std::collections::HashMap<Expr, u64>,
        ) -> Result<(), Error> {
            at.clear();
            for &e in order {
                let v = |x: Expr| at.get(&x).copied().unwrap_or(0);
                let value = if let Some(&(j, complement)) = self.atom_of.get(&e) {
                    let v = if corner >> j & 1 == 1 { ones } else { 0 };
                    if complement { !v } else { v }
                } else {
                    match self.cx.view(e)? {
                        View::Const(c) => c.to_u64().unwrap_or(0),
                        View::Bin(BinOp::And, x, y) => v(x) & v(y),
                        View::Bin(BinOp::Or, x, y) => v(x) | v(y),
                        View::Bin(BinOp::Xor, x, y) => v(x) ^ v(y),
                        View::Bin(BinOp::Add, x, y) => v(x).wrapping_add(v(y)),
                        View::Bin(BinOp::Sub, x, y) => v(x).wrapping_sub(v(y)),
                        View::Bin(BinOp::Mul, x, y) => v(x).wrapping_mul(v(y)),
                        View::Bin(BinOp::Shl, x, k) => {
                            match self.cx.as_const(k)?.and_then(|k| k.to_u64()) {
                                Some(k) if k < 64 => v(x) << k,
                                _ => 0,
                            }
                        }
                        View::Un(UnOp::Not, x) => !v(x),
                        View::Un(UnOp::Neg, x) => v(x).wrapping_neg(),
                        // Not reached: whatever is none of these is an atom.
                        _ => 0,
                    }
                };
                at.insert(e, value & mask);
            }
            Ok(())
        }
    }
    let mut shape = Shape {
        cx,
        w,
        mask,
        atoms: Vec::new(),
        atom_of: Default::default(),
        polys: Default::default(),
        masked: false,
        kinds: Default::default(),
    };
    if shape.kind(a)?.is_none() || shape.kind(b)?.is_none() || shape.atoms.is_empty() {
        return Ok(false);
    }
    let mut facts = Vec::new();
    for &z in zeros {
        if cx.width(z)?.bits() == w && shape.kind(z)? == Some(Kind::Bitwise) {
            facts.push(z);
        }
    }
    if shape.masked {
        facts.clear();
    }
    // (An atom is a node, read the same in both: one found under the other side too is the
    // same variable there.)
    let roots: Vec<Expr> = [a, b].into_iter().chain(facts.iter().copied()).collect();
    let order = shape.order(&roots)?;
    let mut at = std::collections::HashMap::with_capacity(order.len());
    let corners = 1usize << shape.atoms.len();
    if !shape.masked {
        for corner in 0..corners {
            shape.values(&order, corner, mask, mask, &mut at)?;
            if facts.iter().any(|z| at.get(z).is_some_and(|&v| v != 0)) {
                continue;
            }
            if at.get(&a) != at.get(&b) {
                return Ok(false);
            }
        }
        return Ok(true);
    }
    if usize::from(w) * corners * order.len() > CORNER_WORK {
        return Ok(false);
    }
    shape.values(&order, 0, 0, mask, &mut at)?;
    if at.get(&a) != at.get(&b) {
        return Ok(false);
    }
    for bit in 0..u32::from(w) {
        for corner in 1..corners {
            shape.values(&order, corner, 1 << bit, mask, &mut at)?;
            if at.get(&a) != at.get(&b) {
                return Ok(false);
            }
        }
    }
    Ok(true)
}

/// `a` and `b` with every product, quotient and remainder that both contain replaced by a
/// symbol of its own (the outermost ones: what is under one goes with it). Equal after that
/// is equal before it.
#[cfg(feature = "prove")]
fn without_shared_arithmetic(cx: &mut Context, a: Expr, b: Expr) -> Result<(Expr, Expr), Error> {
    use crate::View;
    use crate::ops::BinOp;
    let hard = |cx: &Context, e: Expr| -> Result<bool, Error> {
        Ok(matches!(
            cx.view(e)?,
            View::Bin(
                BinOp::Mul
                    | BinOp::UMulHi
                    | BinOp::SMulHi
                    | BinOp::UDiv
                    | BinOp::URem
                    | BinOp::SDiv
                    | BinOp::SRem,
                _,
                _
            )
        ))
    };
    let in_a: std::collections::HashSet<Expr> = cx.post_order(&[a])?.into_iter().collect();
    let mut map = Vec::new();
    for e in cx.post_order(&[b])? {
        if in_a.contains(&e) && hard(cx, e)? {
            let fresh = cx.fresh_symbol(cx.width(e)?)?;
            map.push((e, fresh));
        }
    }
    if map.is_empty() {
        return Ok((a, b));
    }
    let out = cx.substitute(&[a, b], &map)?;
    Ok((out[0], out[1]))
}

/// `e` with each rewrite's left side replaced by its right, again and again until nothing
/// changes (or, should the rewrites loop, after as many rounds as there are rewrites).
#[cfg(feature = "prove")]
fn normal(cx: &mut Context, e: Expr, rewrites: &[(Expr, Expr)]) -> Result<Expr, Error> {
    let mut current = e;
    for _ in 0..=rewrites.len() {
        let next = cx.substitute(&[current], rewrites)?[0];
        if next == current {
            break;
        }
        current = next;
    }
    Ok(current)
}

/// What [`Derivation::check`] found.
#[cfg(feature = "prove")]
#[derive(Clone, Debug, Default, PartialEq, Eq)]
#[non_exhaustive]
pub struct Checked {
    /// Steps whose two sides were proved equal.
    pub proved: usize,
    /// Of those, the steps proved by arithmetic alone: both sides, as polynomials over the
    /// subexpressions that are not sums, products or negations, are one polynomial modulo
    /// `2^width`; or both are linear combinations of bitwise functions of the same few
    /// subexpressions and agree wherever each of those is all zeros or all ones, which
    /// such combinations cannot do without being equal.
    pub by_ring: usize,
    /// The positions of the steps that were not, within the budget (or because their sides
    /// are equal only where the subexpression's users read it).
    pub unproved: Vec<usize>,
    /// Stretches explained by their steps: rewritten by them, what the stretch began on and
    /// what it left are one expression.
    pub explained: usize,
    /// Of those, the stretches every step of which was proved.
    pub sound: usize,
    /// Stretches not explained by their steps, but whose two ends were proved equal as
    /// wholes.
    pub whole: usize,
    /// The positions of the stretches that are neither: the engine's word is all there is
    /// for them.
    pub open: Vec<usize>,
    /// Whether the stretches follow one another from the expression given to the result.
    pub continuous: bool,
    /// The number of stretches.
    pub stretches: usize,
}

#[cfg(feature = "prove")]
impl Checked {
    /// Whether the result is equal to the expression given on the word of the circuit, the
    /// search, the constructors and the substitution alone: the stretches follow one
    /// another, and each is explained by proved steps or proved as a whole.
    pub fn certified(&self) -> bool {
        self.continuous && self.sound + self.whole == self.stretches
    }
}

#[cfg(feature = "prove")]
impl Derivation {
    /// Checks the derivation in a context of its own, without the engine. Every step's two
    /// sides are proved equal: as polynomials modulo `2^width` over their subexpressions
    /// that are not arithmetic (a few lines of ring arithmetic, which settles the
    /// rearrangements of sums and products a search does not), or else by the circuit and
    /// the search (`cfg`, with the simplifier off whatever it says). A step that repeats is
    /// proved once. Every stretch is replayed:
    /// rewritten by its steps until nothing changes, what the stretch began on and what it
    /// left must become one expression; a stretch they do not explain is proved as a whole
    /// if the search can.
    ///
    /// An unproved step or an open stretch does not refute anything: the search ran out, as
    /// it does on a multiplication of any size, or the pass did not report what it did as
    /// steps that replay.
    pub fn check(&self, cfg: &crate::prove::Config) -> Result<Checked, Error> {
        use crate::prove::{Outcome, equal};
        let cfg = cfg.with_simplify(false);
        let width = |w: u16| Width::new(w).map(ParseOptions::width).map_err(Error::from);
        let whole = width(self.width)?;
        let mut cx = Context::new();
        let mut report = Checked {
            stretches: self.stretches.len(),
            ..Checked::default()
        };
        let mut pairs: Vec<(Expr, Expr, bool)> = Vec::with_capacity(self.steps.len());
        // Per distinct step: proved by the ring (`Some(true)`), by the search, or not.
        let mut known: std::collections::HashMap<(Expr, Expr), Option<bool>> = Default::default();
        for (k, step) in self.steps.iter().enumerate() {
            let o = width(step.width)?;
            let pair = (cx.parse(&step.before, &o)?, cx.parse(&step.after, &o)?);
            // The ring first: what it decides it decides at once, and a rearranged sum of
            // products is what the search is worst at.
            let how = match known.get(&pair) {
                Some(&h) => h,
                None => {
                    let h = if ring_equal(&cx, pair.0, pair.1)?
                        || corners_equal(&cx, pair.0, pair.1)?
                    {
                        Some(true)
                    } else {
                        // With the products and quotients both sides share taken as
                        // unknowns first: equal whatever those are is equal, and a step
                        // that moves bits around a product is then no harder than one that
                        // moves them around a symbol.
                        let (b, a) = without_shared_arithmetic(&mut cx, pair.0, pair.1)?;
                        let proved = |cx: &mut Context, x, y| -> Result<bool, Error> {
                            Ok(matches!(equal(cx, x, y, &cfg)?, Outcome::Proved(_)))
                        };
                        let found = ((b, a) != pair && proved(&mut cx, b, a)?)
                            || proved(&mut cx, pair.0, pair.1)?;
                        found.then_some(false)
                    };
                    known.insert(pair, h);
                    h
                }
            };
            let proved = how.is_some();
            match how {
                Some(by_ring) => {
                    report.proved += 1;
                    report.by_ring += usize::from(by_ring);
                }
                None => report.unproved.push(k),
            }
            pairs.push((pair.0, pair.1, proved));
        }
        let mut at = cx.parse(&self.from, &whole)?;
        report.continuous = true;
        for (k, stretch) in self.stretches.iter().enumerate() {
            let (from, to) = (
                cx.parse(&stretch.from, &whole)?,
                cx.parse(&stretch.to, &whole)?,
            );
            report.continuous &= from == at;
            at = to;
            let mine = pairs.get(stretch.steps.clone()).unwrap_or_default();
            // The steps as rewrites, each read under the ones before it too (the engine
            // reports a step on a subexpression as it stood when the step was made, which
            // an earlier step of the stretch may since have rewritten elsewhere): both ends
            // of the stretch, rewritten by them until nothing changes, must meet.
            let mut rewrites: Vec<(Expr, Expr)> = Vec::with_capacity(2 * mine.len());
            for &(before, after, _) in mine {
                let (b, a) = (
                    normal(&mut cx, before, &rewrites)?,
                    normal(&mut cx, after, &rewrites)?,
                );
                for (x, y) in [(b, a), (before, a)] {
                    if x != y {
                        rewrites.retain(|&(from, _)| from != x);
                        rewrites.push((x, y));
                    }
                }
            }
            if normal(&mut cx, from, &rewrites)? == normal(&mut cx, to, &rewrites)? {
                report.explained += 1;
                report.sound += usize::from(mine.iter().all(|&(_, _, proved)| proved));
            } else if matches!(equal(&mut cx, from, to, &cfg)?, Outcome::Proved(_)) {
                report.whole += 1;
            } else {
                report.open.push(k);
            }
        }
        report.continuous &= at == cx.parse(&self.to, &whole)?;
        Ok(report)
    }

    /// The steps as Lean 4 theorems, one each (`before = after`, proved `by bv_decide`), in
    /// one file: what Lean checks of a derivation is that each of its rewrites is an
    /// equality. A step Lean's `BitVec` cannot state (see
    /// [`prove::lean_theorem`](crate::prove::lean_theorem)) is a comment saying so.
    pub fn lean(&self, name: &str) -> Result<String, Error> {
        let mut out = String::from("import Std.Tactic.BVDecide\n");
        let mut cx = Context::new();
        for (k, step) in self.steps.iter().enumerate() {
            let o = ParseOptions::width(Width::new(step.width)?);
            let (before, after) = (cx.parse(&step.before, &o)?, cx.parse(&step.after, &o)?);
            let theorem = format!("{name}_step_{k}");
            match crate::prove::lean_equation(&mut cx, &theorem, before, after) {
                Ok(t) => {
                    out.push_str(&format!("\n-- Step {k}, by {}.\n{t}", step.by));
                }
                Err(e) => out.push_str(&format!("\n-- Step {k}, by {}: {e}.\n", step.by)),
            }
        }
        Ok(out)
    }
}

#[cfg(all(test, feature = "prove"))]
mod tests {
    use super::*;
    use crate::testutil::Rng;
    use crate::{BitVec, SymbolKey};

    /// The two checks that prove a step without a search say "equal" only of expressions
    /// that are: every pair they accept is compared at every value of its symbols.
    #[test]
    fn the_arithmetic_checks_accept_only_equal_expressions() {
        let w = Width::new(4).unwrap();
        let o = ParseOptions::width(w);
        let mut rng = Rng(0xa1);
        let engine = Engine::standard();
        let (mut ring, mut corners, mut pairs) = (0, 0, 0);
        for round in 0..3000 {
            let mut cx = Context::new();
            let term = |rng: &mut Rng, depth: u32| -> String {
                fn go(rng: &mut Rng, depth: u32) -> String {
                    let leaf = |rng: &mut Rng| match rng.below(5) {
                        0 => "a".to_string(),
                        1 => "b".to_string(),
                        2 => "c".to_string(),
                        3 => format!("{}", rng.below(16)),
                        _ => "(a * b)".to_string(),
                    };
                    if depth == 0 {
                        return leaf(rng);
                    }
                    let (x, y) = (go(rng, depth - 1), go(rng, depth - 1));
                    match rng.below(10) {
                        0 => format!("({x} + {y})"),
                        1 => format!("({x} - {y})"),
                        2 => format!("({x} * {y})"),
                        3 => format!("({x} & {y})"),
                        4 => format!("({x} | {y})"),
                        5 => format!("({x} ^ {y})"),
                        6 => format!("~{x}"),
                        7 => format!("(0 - {x})"),
                        8 => format!("({x} << {})", rng.below(3)),
                        _ => leaf(rng),
                    }
                }
                go(rng, depth)
            };
            let e = cx.parse(&term(&mut rng, 3), &o).unwrap();
            // Against what the engine makes of it (equal, often by these very laws), and
            // against another expression (seldom equal).
            let simplified = engine.simplify(&mut cx, e).unwrap().expr;
            let other = cx.parse(&term(&mut rng, 3), &o).unwrap();
            for (x, y) in [(e, simplified), (e, other), (simplified, other)] {
                pairs += 1;
                let by_ring = ring_equal(&cx, x, y).unwrap();
                let by_corners = corners_equal(&cx, x, y).unwrap();
                ring += u32::from(by_ring && x != y);
                corners += u32::from(by_corners && x != y);
                if !(by_ring || by_corners) {
                    continue;
                }
                for point in 0..1u32 << 12 {
                    let env = crate::FnEnv(|key: &SymbolKey, _| {
                        let k = match key {
                            SymbolKey::Str(s) => u32::from(s.as_bytes()[0] - b'a'),
                            _ => 0,
                        };
                        Some(BitVec::wrapping_from_u64(
                            w,
                            u64::from(point >> (4 * k) & 15),
                        ))
                    });
                    let v = cx.eval(&[x, y], &env).unwrap();
                    assert_eq!(
                        v[0],
                        v[1],
                        "round {round}: {} and {} (ring {by_ring}, corners {by_corners})",
                        cx.display(x),
                        cx.display(y)
                    );
                }
            }
        }
        // Both were exercised on pairs that are not one node.
        assert!(ring > 100 && corners > 100, "{ring} {corners} of {pairs}");
    }

    /// A linear MBA with masks inside is decided by its values one bit at a time.
    #[test]
    #[cfg(feature = "prove")]
    fn a_masked_linear_mba_is_equal_by_its_corners() {
        let o = ParseOptions::width(Width::W64);
        let mut cx = Context::new();
        let mut equal = |a: &str, b: &str| {
            let (a, b) = (cx.parse(a, &o).unwrap(), cx.parse(b, &o).unwrap());
            corners_equal(&cx, a, b).unwrap()
        };
        // From a deobfuscator's log: the masks are complements, and so are the two terms.
        assert!(equal(
            "(x & 0xd45e8a06a619d390) - (~x & 0x2ba175f959e62c6f) * 0x764a54eb3b553b4a \
             - (x & 0x2ba175f959e62c6f) * 0x764a54eb3b553b4b + 0x4e1724930687e7a6",
            "0x9d21013e4e004e20 - (x ^ 0xd45e8a06a619d390)"
        ));
        // Over an opaque part, here a product.
        assert!(equal(
            "(x * y ^ 0x501020403650420) * 6 + (x * y ^ 0xfafefdfbfc9afbdf) * 6",
            "-6"
        ));
        assert!(equal(
            "(x & 0xf0) + (x & 0x0f) + (y | 3)",
            "(x & 0xff) + (y & -4) + 3"
        ));
        // A sum under a mask is an atom, and `c - s` is the complement of `s + (-1 - c)`.
        assert!(equal(
            "(x * y + 7 & 0xff00) + (-8 - x * y & 0xff00)",
            "0xff00"
        ));
        assert!(equal("(x + y & z) + (x + y | z)", "x + y + z"));
        assert!(!equal("(x + y & 0xff00) + (-7 - x - y & 0xff00)", "0xff00"));
        // One bit off.
        assert!(!equal("(x & 0xf0) + (x & 0x0f)", "x & 0x1ff"));
        assert!(!equal("(x & 0xf0) + (x & 0x1f)", "x & 0xff"));
    }
}
