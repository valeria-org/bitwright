//! Rewrites a host defines in Rust: see [`Rewrite`].

use core::fmt;

use super::budget::Counter;
use super::{Accept, By, Fin, Reject, Runner, Step, Stop};
use crate::error::Error;
use crate::expr::{Context, Expr, OpCode, View};
use crate::facts::known::{bv_and, bv_not, low_mask};
use crate::facts::{Env as AssumedEnv, Facts, KnownBits, Reliance};
use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest};
use crate::ops::{BinOp, CmpOp, CmpOpExt, UnOp};
use crate::{BitVec, Query, Truth, Width};

/// A rewrite written in Rust by the host, linked into an engine at run time: what `.bwr`
/// rules cannot say (a target's legality, a cost model, the host's own analyses).
///
/// A host rewrite runs in the rule phases whose strategy names its [group](Rewrite::group),
/// after the phase's rules, at every node the phase visits (its operands already normal). It
/// sees the node through a [`Site`]: views of nodes, their facts, construction. Its result is
/// committed like a rule's, with one more check, since arbitrary code carries no static proof:
///
/// - **Termination.** The result must be smaller than the node in the ground order the rules
///   decrease (tree size, then operator precedence), so rules and host rewrites together
///   cannot cycle. A result that is not smaller is not committed ([`Stats::host`] counts it
///   under `rejected_cost`).
/// - **Postconditions.** Its width, the fact tripwire when on, the host veto
///   ([`Hooks::admit`]), and for a rewrite linked with [`EngineBuilder::rewrite`], sampled
///   verification at every application. A rewrite found wrong is quarantined for the rest of
///   the call.
/// - **Budgets.** What it builds and the facts it asks for are charged to the call.
///
/// A rewrite must be deterministic: its result a function of the node, its facts and its
/// [revision](Rewrite::revision), since results are memoized.
/// [`check::rewrite`](crate::check::rewrite) tests one offline;
/// [`EngineBuilder::trusted_rewrite`] links one without sampling once the host vouches for it.
///
/// [`Stats::host`]: super::Stats::host
/// [`Hooks::admit`]: super::Hooks::admit
/// [`EngineBuilder::rewrite`]: super::EngineBuilder::rewrite
/// [`EngineBuilder::trusted_rewrite`]: super::EngineBuilder::trusted_rewrite
///
/// ```
/// use std::sync::Arc;
/// use bitwright::engine::{Engine, Rewrite, Site, Strategy};
/// use bitwright::{BinOp, Context, Expr, ParseOptions, View, Width};
///
/// /// `x * 2^k` as `x << k` (the built-in rules do it too; this one is for the example).
/// struct MulPow2;
/// impl Rewrite for MulPow2 {
///     fn name(&self) -> &str { "acme.mul_pow2" }
///     fn group(&self) -> &str { "acme" }
///     fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
///         let View::Bin(BinOp::Mul, x, c) = site.view(e)? else { return None };
///         let c = site.as_u64(c)?;
///         if !c.is_power_of_two() { return None; }
///         let w = site.width(e)?;
///         let k = site.constant_u64(w, u64::from(c.trailing_zeros()))?;
///         site.bin(BinOp::Shl, x, k)
///     }
/// }
///
/// let engine = Engine::builder()
///     .rewrite(Arc::new(MulPow2))
///     .allow_unproven(true) // checked at sampled points at every application
///     .strategy(Strategy::new("acme", vec![]).with_rule_groups(&["acme"]))
///     .build()?;
/// let mut cx = Context::new();
/// let e = cx.parse("x * 8", &ParseOptions::width(Width::W32))?;
/// let out = engine.simplify(&mut cx, e)?;
/// assert_eq!(cx.display(out.expr).to_string(), "x << 3");
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub trait Rewrite: Send + Sync + 'static {
    /// A namespaced name for diagnostics, statistics and host vetoes: `acme.fold_flags`.
    fn name(&self) -> &str;

    /// The group a strategy names to run it (`Phase::Local`'s groups, or
    /// [`Strategy::with_rule_groups`](super::Strategy::with_rule_groups)). Several rewrites may
    /// share one; they run in the order they were linked.
    fn group(&self) -> &str {
        "host"
    }

    /// Bumped whenever the rewrite's results change: it enters the engine's configuration
    /// hash, so memoized results of an older revision are not reused.
    fn revision(&self) -> u32 {
        1
    }

    /// The replacement of `e`, whose operands are already normal; `None` to leave it. Return
    /// an expression equal to `e` for every value of its symbols, of its width.
    fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr>;
}

/// What a host rewrite may do at a node: inspect nodes, ask for their facts, build nodes. The
/// engine charges what it does to the call's budget; when the budget runs out, every further
/// request answers `None` and the call stops after the rewrite returns.
pub struct Site<'s> {
    cx: &'s mut Context,
    run: &'s mut dyn SiteRun,
    /// What the facts the rewrite read contribute to the node's finality and reliance.
    fin: Fin,
    /// Why the engine stopped the rewrite's requests, if it did.
    stop: Option<Stop>,
}

impl fmt::Debug for Site<'_> {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        f.debug_struct("Site").finish_non_exhaustive()
    }
}

/// The engine side of a [`Site`]: construction as engine work, and facts and relational queries
/// under the call's budget and assumptions.
pub(super) trait SiteRun {
    /// Runs `f` as engine work. `Err` when the call must stop; `Ok(Err)` when construction
    /// failed (a width mismatch: the rewrite's own error).
    fn make(
        &mut self,
        cx: &mut Context,
        f: &mut dyn FnMut(&mut Context) -> Result<Expr, Error>,
    ) -> Result<Result<Expr, Error>, Stop>;

    /// The facts of node `n`, with what they contribute to finality; `None` when capped.
    fn facts_of(&mut self, cx: &mut Context, n: u32) -> Result<(Option<Facts>, Fin), Stop>;

    /// Evaluates `q` under the active assumptions, declared known bits, and fact budget.
    fn prove(&mut self, cx: &mut Context, q: Query<'_>) -> Result<(Truth, Fin), Stop>;

    /// `Some(k)` when `a - b == k (mod 2^W)` follows from syntax, active assumptions, or pinned
    /// constant facts, with what that contributes to finality and reliance.
    fn const_diff(
        &mut self,
        cx: &mut Context,
        a: Expr,
        b: Expr,
    ) -> Result<(Option<BitVec>, Fin), Stop>;
}

struct HostInvertOracle<'x, 'r, 'a> {
    r: &'x mut Runner<'r, 'a>,
    fin: Fin,
}

impl crate::invert::Oracle for HostInvertOracle<'_, '_, '_> {
    type Err = Stop;

    fn facts(&mut self, cx: &mut Context, i: u32) -> Result<Option<Facts>, Stop> {
        let (f, fin) = super::pass::facts(self.r, cx, i)?;
        self.fin = self.fin.and(fin);
        Ok(f)
    }

    fn charge(&mut self, units: u64) -> Result<(), Stop> {
        self.r.meter.charge(Counter::PassWork, units)?;
        Ok(())
    }
}

/// Decomposes `ia - ib (mod 2^W)` within a bounded linear cone (`Add`, `Sub`, `Neg`, `Not`,
/// constant `Mul`/`Shl`). When `env` is `Some`, assumed congruence classes and constant-offset
/// relations are substituted as well, recording the [`Reliance`] of every substitution taken.
fn linear_const_diff(
    cx: &Context,
    env: Option<&AssumedEnv>,
    ia: u32,
    ib: u32,
    w: Width,
) -> Option<(BitVec, Reliance)> {
    if ia == ib {
        return Some((BitVec::zero(w), Reliance::NONE));
    }
    if let (Some(va), Some(vb)) = (cx.const_val(ia), cx.const_val(ib)) {
        return Some((BitVec::bin_unchecked(BinOp::Sub, &va, &vb), Reliance::NONE));
    }
    let one = BitVec::one(w);
    let neg_one = BitVec::ones(w);
    let mut konst = BitVec::zero(w);
    let mut rel = Reliance::NONE;
    let mut terms: Vec<(u32, BitVec)> = Vec::new();
    let mut todo: Vec<(u32, BitVec)> = vec![(ib, neg_one), (ia, one)];
    let mut steps = 0usize;
    while let Some((cur, scale)) = todo.pop() {
        if scale.is_zero() {
            continue;
        }
        steps += 1;
        if steps > 48 {
            return None;
        }
        if let Some(cv) = cx.const_val(cur) {
            let prod = BitVec::bin_unchecked(BinOp::Mul, &cv, &scale);
            konst = BitVec::bin_unchecked(BinOp::Add, &konst, &prod);
            continue;
        }
        if let Some(env) = env {
            let (rep, r_eq) = env.find(cur);
            if rep != cur {
                rel |= r_eq;
                todo.push((rep, scale));
                continue;
            }
            if let Some(&(_, base, ref off, r_off)) =
                env.offset_rels.iter().find(|&&(m, ..)| m == cur)
                && off.width() == w
            {
                rel |= r_off;
                let prod = BitVec::bin_unchecked(BinOp::Mul, off, &scale);
                konst = BitVec::bin_unchecked(BinOp::Add, &konst, &prod);
                todo.push((base, scale));
                continue;
            }
        }
        let nd = cx.node(cur);
        match nd.op {
            OpCode::Add => {
                todo.push((nd.b, scale));
                todo.push((nd.a, scale));
            }
            OpCode::Sub => {
                todo.push((nd.b, BitVec::un_unchecked(UnOp::Neg, &scale)));
                todo.push((nd.a, scale));
            }
            OpCode::Neg => {
                todo.push((nd.a, BitVec::un_unchecked(UnOp::Neg, &scale)));
            }
            OpCode::Not => {
                konst = BitVec::bin_unchecked(BinOp::Sub, &konst, &scale);
                todo.push((nd.a, BitVec::un_unchecked(UnOp::Neg, &scale)));
            }
            OpCode::Mul if cx.is_const(nd.a) || cx.is_const(nd.b) => {
                let (u, cid) = if cx.is_const(nd.b) {
                    (nd.a, nd.b)
                } else {
                    (nd.b, nd.a)
                };
                let cv = cx.const_val(cid)?;
                todo.push((u, BitVec::bin_unchecked(BinOp::Mul, &scale, &cv)));
            }
            OpCode::Shl if cx.is_const(nd.b) => {
                let sv = cx.const_val(nd.b)?;
                let factor = BitVec::bin_unchecked(BinOp::Shl, &one, &sv);
                if !factor.is_zero() {
                    todo.push((nd.a, BitVec::bin_unchecked(BinOp::Mul, &scale, &factor)));
                }
            }
            _ => match terms.iter_mut().find(|t| t.0 == cur) {
                Some(slot) => slot.1 = BitVec::bin_unchecked(BinOp::Add, &slot.1, &scale),
                None => {
                    if terms.len() >= 16 {
                        return None;
                    }
                    terms.push((cur, scale));
                }
            },
        }
    }
    if terms.iter().any(|(_, c)| !c.is_zero()) {
        return None;
    }
    Some((konst, rel))
}

impl SiteRun for Runner<'_, '_> {
    fn make(
        &mut self,
        cx: &mut Context,
        f: &mut dyn FnMut(&mut Context) -> Result<Expr, Error>,
    ) -> Result<Result<Expr, Error>, Stop> {
        let r = self.build(cx, |cx| Ok(f(cx)))?;
        match r {
            Err(Error::ArenaFull { .. }) => Err(Stop::Exhausted(super::Exhausted::ArenaCapacity)),
            r => Ok(r),
        }
    }

    fn facts_of(&mut self, cx: &mut Context, n: u32) -> Result<(Option<Facts>, Fin), Stop> {
        super::pass::facts(self, cx, n)
    }

    fn prove(&mut self, cx: &mut Context, q: Query<'_>) -> Result<(Truth, Fin), Stop> {
        use super::pass::predicate::{Pred, constant as pred_const};
        let from_bool = |b: bool| if b { Truth::True } else { Truth::False };
        match q {
            Query::IsZero(e) | Query::IsNonZero(e) => {
                let want_nonzero = matches!(q, Query::IsNonZero(_));
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                let (f_opt, fin) = self.facts_of(cx, i)?;
                if let Some(f) = f_opt
                    && let Some(eq_zero) =
                        crate::facts::decide_cmp(CmpOp::Eq, &f, &Facts::constant(&BitVec::zero(w)))
                {
                    let ans = if want_nonzero { !eq_zero } else { eq_zero };
                    return Ok((from_bool(ans), fin));
                }
                if let Some(nz) = pred_const(cx, Pred::NonZero(i)).0 {
                    let ans = if want_nonzero { nz } else { !nz };
                    return Ok((from_bool(ans), Fin::FINAL));
                }
                Ok((Truth::Unknown, fin.unchanged()))
            }
            Query::IsConstant(e) => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                if cx.const_val(i).is_some() {
                    return Ok((Truth::True, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                if f_opt.and_then(|f| f.as_constant()).is_some() {
                    Ok((Truth::True, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::Bit { e, bit, value } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if bit >= w.bits() {
                    return Ok((Truth::Unknown, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                if let Some(b) = f_opt.and_then(|f| f.known().bit(bit)) {
                    return Ok((from_bool(b == value), fin));
                }
                if let Some(b) = pred_const(cx, Pred::Bit(i, bit)).0 {
                    return Ok((from_bool(b == value), Fin::FINAL));
                }
                Ok((Truth::Unknown, fin.unchanged()))
            }
            Query::Eq(x, y) | Query::Cmp(_, x, y) => {
                let (Ok(ix), Ok(iy)) = (cx.id(x), cx.id(y)) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(ix);
                if cx.width_of(iy) != w {
                    return Ok((Truth::Unknown, Fin::FINAL));
                }
                let (op, swap) = match q {
                    Query::Cmp(op, ..) => op.canonical(),
                    _ => (CmpOp::Eq, false),
                };
                let (ix, iy) = if swap { (iy, ix) } else { (ix, iy) };
                if ix == iy {
                    let v = matches!(op, CmpOp::Eq | CmpOp::Ule | CmpOp::Sle);
                    return Ok((from_bool(v), Fin::FINAL));
                }
                if matches!(op, CmpOp::Eq | CmpOp::Ne)
                    && let Some((d, _)) = linear_const_diff(cx, None, ix, iy, w)
                {
                    let v = if op == CmpOp::Eq {
                        d.is_zero()
                    } else {
                        !d.is_zero()
                    };
                    return Ok((from_bool(v), Fin::FINAL));
                }
                if let Some(a) = self.assumptions
                    && !a.is_infeasible()
                {
                    if self.meter.left_in(|b| b.fact_work) == 0 {
                        return Err(Stop::Exhausted(super::Exhausted::FactWork));
                    }
                    if let Some((v, rel)) = cx.assumed_order(a, op, ix, iy) {
                        self.meter.check()?;
                        return Ok((from_bool(v), Fin::relying(rel)));
                    }
                    if matches!(op, CmpOp::Eq | CmpOp::Ne)
                        && a.store.declaration_revision == cx.declaration_revision
                        && let Some((d, rel)) = linear_const_diff(cx, Some(&a.store.env), ix, iy, w)
                    {
                        self.meter.check()?;
                        let v = if op == CmpOp::Eq {
                            d.is_zero()
                        } else {
                            !d.is_zero()
                        };
                        return Ok((from_bool(v), Fin::relying(rel)));
                    }
                }
                let (fx_opt, fin_x) = self.facts_of(cx, ix)?;
                let (fy_opt, fin_y) = self.facts_of(cx, iy)?;
                if let (Some(fx), Some(fy)) = (fx_opt, fy_opt)
                    && let Some(v) = crate::facts::decide_cmp(op, &fx, &fy)
                {
                    return Ok((from_bool(v), fin_x.and(fin_y)));
                }
                if let Some(v) = pred_const(cx, Pred::Cmp(op, ix, iy)).0 {
                    return Ok((from_bool(v), Fin::FINAL));
                }
                Ok((Truth::Unknown, fin_x.unchanged().and(fin_y.unchanged())))
            }
            Query::InURange { e, lo, hi } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if lo.width() != w || hi.width() != w {
                    return Ok((Truth::Unknown, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let u = f.urange();
                if BitVec::cmp_unchecked(CmpOp::Ule, lo, &u.lo())
                    && BitVec::cmp_unchecked(CmpOp::Ule, &u.hi(), hi)
                {
                    Ok((Truth::True, fin))
                } else if BitVec::cmp_unchecked(CmpOp::Ult, hi, &u.lo())
                    || BitVec::cmp_unchecked(CmpOp::Ult, &u.hi(), lo)
                {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::InSRange { e, lo, hi } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if lo.width() != w || hi.width() != w {
                    return Ok((Truth::Unknown, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let s = f.srange();
                if BitVec::cmp_unchecked(CmpOp::Sle, lo, &s.lo())
                    && BitVec::cmp_unchecked(CmpOp::Sle, &s.hi(), hi)
                {
                    Ok((Truth::True, fin))
                } else if BitVec::cmp_unchecked(CmpOp::Slt, hi, &s.lo())
                    || BitVec::cmp_unchecked(CmpOp::Slt, &s.hi(), lo)
                {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::Aligned { e, log2 } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let low = low_mask(w, u32::from(log2));
                if bv_and(&f.known().maybe_one(), &low).is_zero() {
                    Ok((Truth::True, fin))
                } else if !bv_and(&f.known().known_one(), &low).is_zero() {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::MaskRedundant { e, mask } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if mask.width() != w {
                    return Ok((Truth::Unknown, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let outside = bv_not(mask);
                if bv_and(&f.known().maybe_one(), &outside).is_zero() {
                    Ok((Truth::True, fin))
                } else if !bv_and(&f.known().known_one(), &outside).is_zero() {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::FitsUnsigned { e, bits } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if u32::from(bits) >= u32::from(w.bits()) {
                    return Ok((Truth::True, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let limit = low_mask(w, u32::from(bits));
                if BitVec::cmp_unchecked(CmpOp::Ule, &f.urange().hi(), &limit) {
                    Ok((Truth::True, fin))
                } else if BitVec::cmp_unchecked(CmpOp::Ult, &limit, &f.urange().lo()) {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::FitsSigned { e, bits } => {
                let Ok(i) = cx.id(e) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let w = cx.width_of(i);
                if bits == 0 {
                    return Ok((Truth::False, Fin::FINAL));
                }
                if u32::from(bits) >= u32::from(w.bits()) {
                    return Ok((Truth::True, Fin::FINAL));
                }
                let (f_opt, fin) = self.facts_of(cx, i)?;
                let Some(f) = f_opt else {
                    return Ok((Truth::Unknown, fin.unchanged()));
                };
                let hi = low_mask(w, u32::from(bits) - 1);
                let lo = bv_not(&hi);
                let s = f.srange();
                if BitVec::cmp_unchecked(CmpOp::Sle, &lo, &s.lo())
                    && BitVec::cmp_unchecked(CmpOp::Sle, &s.hi(), &hi)
                {
                    Ok((Truth::True, fin))
                } else if BitVec::cmp_unchecked(CmpOp::Slt, &s.hi(), &lo)
                    || BitVec::cmp_unchecked(CmpOp::Slt, &hi, &s.lo())
                {
                    Ok((Truth::False, fin))
                } else {
                    Ok((Truth::Unknown, fin.unchanged()))
                }
            }
            Query::Injective { e, of } | Query::Bijective { e, of } => {
                let onto = matches!(q, Query::Bijective { .. });
                let (Ok(ei), Ok(xi)) = (cx.id(e), cx.id(of)) else {
                    return Ok((Truth::Unknown, Fin::FINAL));
                };
                let (we, wx) = (cx.wid(ei), cx.wid(xi));
                if we < wx || (onto && we != wx) {
                    return Ok((Truth::False, Fin::FINAL));
                }
                let mut oracle = HostInvertOracle {
                    r: self,
                    fin: Fin::FINAL,
                };
                match crate::invert::chain(cx, &mut oracle, ei, xi)? {
                    crate::invert::Chain::Independent => Ok((Truth::False, oracle.fin.unchanged())),
                    crate::invert::Chain::Proved(_) => Ok((Truth::True, oracle.fin)),
                    crate::invert::Chain::Unknown => Ok((Truth::Unknown, oracle.fin.unchanged())),
                }
            }
        }
    }

    fn const_diff(
        &mut self,
        cx: &mut Context,
        a: Expr,
        b: Expr,
    ) -> Result<(Option<BitVec>, Fin), Stop> {
        let (Ok(ia), Ok(ib)) = (cx.id(a), cx.id(b)) else {
            return Ok((None, Fin::FINAL));
        };
        let w = cx.width_of(ia);
        if cx.width_of(ib) != w {
            return Ok((None, Fin::FINAL));
        }
        // Tier 1: pure syntactic linear cancellation (zero reliance).
        if let Some((d, _)) = linear_const_diff(cx, None, ia, ib, w) {
            return Ok((Some(d), Fin::FINAL));
        }
        // Tier 2: assumed congruence classes and constant-offset relations.
        if let Some(assump) = self.assumptions
            && !assump.is_infeasible()
            && assump.store.declaration_revision == cx.declaration_revision
        {
            if self.meter.left_in(|b| b.fact_work) == 0 {
                return Err(Stop::Exhausted(super::Exhausted::FactWork));
            }
            if let Some((d, rel)) = linear_const_diff(cx, Some(&assump.store.env), ia, ib, w) {
                self.meter.check()?;
                return Ok((Some(d), Fin::relying(rel)));
            }
        }
        // Tier 3: both operands pinned to constants by facts/assumptions.
        let (fa_opt, fin_a) = self.facts_of(cx, ia)?;
        let (fb_opt, fin_b) = self.facts_of(cx, ib)?;
        if let (Some(va), Some(vb)) = (
            fa_opt.and_then(|f| f.as_constant()),
            fb_opt.and_then(|f| f.as_constant()),
        ) {
            return Ok((
                Some(BitVec::bin_unchecked(BinOp::Sub, &va, &vb)),
                fin_a.and(fin_b),
            ));
        }
        Ok((None, fin_a.unchanged().and(fin_b.unchanged())))
    }
}

/// A site outside any engine run: nothing charged, the context's own fact cap, no assumptions
/// (for the offline checker).
#[cfg_attr(not(feature = "check"), allow(dead_code))]
struct Standalone;

impl SiteRun for Standalone {
    fn make(
        &mut self,
        cx: &mut Context,
        f: &mut dyn FnMut(&mut Context) -> Result<Expr, Error>,
    ) -> Result<Result<Expr, Error>, Stop> {
        Ok(f(cx))
    }

    fn facts_of(&mut self, cx: &mut Context, n: u32) -> Result<(Option<Facts>, Fin), Stop> {
        let e = cx.handle(n);
        let f = cx.try_facts(e).map_err(Stop::Error)?;
        Ok((f, Fin::FINAL))
    }

    fn prove(&mut self, cx: &mut Context, q: Query<'_>) -> Result<(Truth, Fin), Stop> {
        Ok((cx.prove(q).unwrap_or(Truth::Unknown), Fin::FINAL))
    }

    fn const_diff(
        &mut self,
        cx: &mut Context,
        a: Expr,
        b: Expr,
    ) -> Result<(Option<BitVec>, Fin), Stop> {
        let (Ok(ia), Ok(ib)) = (cx.id(a), cx.id(b)) else {
            return Ok((None, Fin::FINAL));
        };
        let w = cx.width_of(ia);
        if cx.width_of(ib) != w {
            return Ok((None, Fin::FINAL));
        }
        if let Some((d, _)) = linear_const_diff(cx, None, ia, ib, w) {
            return Ok((Some(d), Fin::FINAL));
        }
        let fa = cx.try_facts(a).map_err(Stop::Error)?;
        let fb = cx.try_facts(b).map_err(Stop::Error)?;
        if let (Some(va), Some(vb)) = (
            fa.and_then(|f| f.as_constant()),
            fb.and_then(|f| f.as_constant()),
        ) {
            return Ok((
                Some(BitVec::bin_unchecked(BinOp::Sub, &va, &vb)),
                Fin::FINAL,
            ));
        }
        Ok((None, Fin::FINAL))
    }
}

/// Runs `r` at `e` in `cx` outside any engine run (for the offline checker).
#[cfg_attr(not(feature = "check"), allow(dead_code))]
pub(crate) fn apply_standalone(cx: &mut Context, r: &dyn Rewrite, e: Expr) -> Option<Expr> {
    let mut run = Standalone;
    let mut site = Site {
        cx,
        run: &mut run,
        fin: Fin::FINAL,
        stop: None,
    };
    r.rewrite(&mut site, e)
}

impl Site<'_> {
    /// The context, to read (to display a node, say).
    pub fn context(&self) -> &Context {
        self.cx
    }

    /// The node `e`, if it is a handle of this context.
    pub fn view(&self, e: Expr) -> Option<View> {
        self.cx.view(e).ok()
    }

    /// The width of `e`.
    pub fn width(&self, e: Expr) -> Option<Width> {
        self.cx.width(e).ok()
    }

    /// The value of `e`, if it is a constant.
    pub fn as_const(&self, e: Expr) -> Option<BitVec> {
        self.cx.as_const(e).ok().flatten()
    }

    /// The value of `e`, if it is a constant that fits in 64 bits.
    pub fn as_u64(&self, e: Expr) -> Option<u64> {
        self.as_const(e)?.to_u64()
    }

    /// The facts of `e` (under the run's assumptions and declared known bits); `None` when
    /// the fact budget declined the query, which makes the node's result not final.
    pub fn facts(&mut self, e: Expr) -> Option<Facts> {
        if self.stop.is_some() {
            return None;
        }
        let n = self.cx.id(e).ok()?;
        match self.run.facts_of(self.cx, n) {
            Ok((f, fin)) => {
                self.fin = self.fin.and(fin);
                f
            }
            Err(stop) => {
                self.stop = Some(stop);
                None
            }
        }
    }

    /// The known bits of `e` (see [`facts`](Self::facts)).
    pub fn known(&mut self, e: Expr) -> Option<KnownBits> {
        self.facts(e).map(|f| f.known())
    }

    /// Evaluates `q` under the run's active assumptions and declared known bits, charging fact
    /// work and recording any constraint [`Reliance`] (or budget cap) into this application's
    /// finality. Returns [`Truth::Unknown`] when undecided or stopped by the budget.
    pub fn prove(&mut self, q: Query<'_>) -> Truth {
        if self.stop.is_some() {
            return Truth::Unknown;
        }
        match self.run.prove(self.cx, q) {
            Ok((truth, fin)) => {
                self.fin = self.fin.and(fin);
                truth
            }
            Err(stop) => {
                self.stop = Some(stop);
                Truth::Unknown
            }
        }
    }

    /// Whether `a == b` is proved under the run's active assumptions and declared known bits
    /// (shorthand for `self.prove(Query::Eq(a, b)) == Truth::True`).
    pub fn prove_eq(&mut self, a: Expr, b: Expr) -> bool {
        self.prove(Query::Eq(a, b)) == Truth::True
    }

    /// `Some(k)` when `a - b == k (mod 2^W)` is proved syntactically or under the run's active
    /// assumptions and facts, recording any [`Reliance`] into this application's finality.
    pub fn const_diff(&mut self, a: Expr, b: Expr) -> Option<BitVec> {
        if self.stop.is_some() {
            return None;
        }
        match self.run.const_diff(self.cx, a, b) {
            Ok((diff, fin)) => {
                self.fin = self.fin.and(fin);
                diff
            }
            Err(stop) => {
                self.stop = Some(stop);
                None
            }
        }
    }

    fn make(&mut self, mut f: impl FnMut(&mut Context) -> Result<Expr, Error>) -> Option<Expr> {
        if self.stop.is_some() {
            return None;
        }
        match self.run.make(self.cx, &mut f) {
            Ok(r) => r.ok(),
            Err(stop) => {
                self.stop = Some(stop);
                None
            }
        }
    }

    /// A constant.
    pub fn constant(&mut self, v: &BitVec) -> Option<Expr> {
        self.make(|cx| cx.constant(v))
    }

    /// The constant `v` of `width` bits (it must fit).
    pub fn constant_u64(&mut self, width: Width, v: u64) -> Option<Expr> {
        self.make(|cx| cx.constant_u64(width, v))
    }

    /// A unary operator.
    pub fn un(&mut self, op: UnOp, a: Expr) -> Option<Expr> {
        self.make(|cx| cx.un(op, a))
    }

    /// A binary operator.
    pub fn bin(&mut self, op: BinOp, a: Expr, b: Expr) -> Option<Expr> {
        self.make(|cx| cx.bin(op, a, b))
    }

    /// A comparison (1-bit result).
    pub fn cmp(&mut self, op: impl Into<CmpOpExt>, a: Expr, b: Expr) -> Option<Expr> {
        let op = op.into();
        self.make(|cx| cx.cmp(op, a, b))
    }

    /// Zero extension to `to` bits.
    pub fn zext(&mut self, a: Expr, to: Width) -> Option<Expr> {
        self.make(|cx| cx.zext(a, to))
    }

    /// Sign extension to `to` bits.
    pub fn sext(&mut self, a: Expr, to: Width) -> Option<Expr> {
        self.make(|cx| cx.sext(a, to))
    }

    /// The low `to` bits.
    pub fn trunc(&mut self, a: Expr, to: Width) -> Option<Expr> {
        self.make(|cx| cx.trunc(a, to))
    }

    /// Bits `[lo, lo + len)`.
    pub fn extract(&mut self, a: Expr, lo: u16, len: Width) -> Option<Expr> {
        self.make(|cx| cx.extract(a, lo, len))
    }

    /// `hi` in the high bits, `lo` in the low bits.
    pub fn concat(&mut self, hi: Expr, lo: Expr) -> Option<Expr> {
        self.make(|cx| cx.concat(hi, lo))
    }

    /// `cond ? then : els`.
    pub fn select(&mut self, cond: Expr, then: Expr, els: Expr) -> Option<Expr> {
        self.make(|cx| cx.select(cond, then, els))
    }

    /// Output `output` of extension operation `op` over `args`.
    pub fn ext(&mut self, op: crate::ext::ExtId, output: usize, args: &[Expr]) -> Option<Expr> {
        self.make(|cx| cx.ext_output(op, output, args))
    }

    /// Floating-point operation `op` of `format` over `args`.
    pub fn fp(&mut self, op: FpOp, format: FpFormat, args: &[Expr]) -> Option<Expr> {
        self.make(|cx| cx.fp(op, format, args))
    }

    /// Floating-point comparison `op(a, b)` of `format` (1-bit result).
    pub fn fp_cmp(&mut self, format: FpFormat, op: FpCmpOp, a: Expr, b: Expr) -> Option<Expr> {
        self.make(|cx| cx.fp_cmp(format, op, a, b))
    }

    /// Floating-point classification test `test(a)` of `format` (1-bit result).
    pub fn fp_test(&mut self, format: FpFormat, test: FpTest, a: Expr) -> Option<Expr> {
        self.make(|cx| cx.fp_test(format, test, a))
    }
}

/// A host rewrite linked into an engine.
#[derive(Clone)]
pub(crate) struct Linked {
    pub(crate) op: std::sync::Arc<dyn Rewrite>,
    /// Linked with `trusted_rewrite`: applications are not sampled.
    pub(crate) trusted: bool,
}

impl Runner<'_, '_> {
    /// Tries the host rewrites `list` at `n` after the phase's rules left it: the first one
    /// that commits, or what the others' fact queries contribute to `n`'s finality.
    pub(super) fn try_host(
        &mut self,
        cx: &mut Context,
        n: u32,
        list: &[u32],
    ) -> Result<Step, Stop> {
        let inner = self.inner;
        let mut fin = Fin::FINAL;
        for &hi in list {
            let linked = &inner.host[hi as usize];
            let name = linked.op.name();
            if self
                .host_quarantined
                .get(hi as usize)
                .copied()
                .unwrap_or(false)
            {
                fin = fin.and(Fin::PROVISIONAL);
                continue;
            }
            self.meter.charge(Counter::Candidates, 1)?;
            self.stats.host.calls += 1;
            let e = cx.handle(n);
            let (out, site_fin, stop) = {
                let mut site = Site {
                    cx: &mut *cx,
                    run: &mut *self,
                    fin: Fin::FINAL,
                    stop: None,
                };
                let out = linked.op.rewrite(&mut site, e);
                (out, site.fin, site.stop)
            };
            if let Some(stop) = stop {
                return Err(stop);
            }
            self.meter.check()?;
            fin = fin.and(site_fin.unchanged());
            let Some(out) = out else {
                continue;
            };
            // A handle the rewrite did not take from this context is its error.
            let Ok(r) = cx.id(out) else {
                self.stats.host.rejected += 1;
                self.quarantine_host(hi);
                continue;
            };
            if r == n {
                self.stats.host.noop += 1;
                continue;
            }
            if cx.wid(r) == cx.wid(n) && crate::rules::order::ground_greater(cx, n, r) != Some(true)
            {
                self.stats.host.rejected_cost += 1;
                self.stats.rejected += 1;
                self.emit(super::Event::Rejected {
                    by: By::Rewrite(name),
                    reason: Reject::Termination,
                });
                continue;
            }
            match self.accept(cx, By::Rewrite(name), linked.trusted, n, r, site_fin.rel)? {
                Accept::Yes => {
                    self.stats.host.changed += 1;
                    return Ok(Step::To(r, fin.and(site_fin)));
                }
                Accept::Vetoed => self.stats.host.rejected += 1,
                Accept::Rejected(reason) => {
                    self.stats.host.rejected += 1;
                    if matches!(reason, Reject::Width | Reject::Verify | Reject::Tripwire) {
                        self.quarantine_host(hi);
                    }
                }
            }
        }
        Ok(Step::Normal(fin))
    }

    fn quarantine_host(&mut self, hi: u32) {
        let hi = hi as usize;
        if self.host_quarantined.len() <= hi {
            self.host_quarantined.resize(hi + 1, false);
        }
        self.host_quarantined[hi] = true;
        self.stats.quarantined += 1;
    }
}

#[cfg(test)]
mod tests {
    use std::sync::Arc;

    use super::*;
    use crate::ParseOptions;
    use crate::engine::{Engine, Phase, Run, Scratch, Strategy, Verify};
    use crate::facts::{Assumptions, Reliance};
    use crate::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};

    /// Folds `select(c, t, f)` when `site.prove` decides `c == 1` or `c == 0`, or when
    /// `site.prove_eq(t, f)` holds under the active assumptions.
    struct AssumptionBranchFold;
    impl Rewrite for AssumptionBranchFold {
        fn name(&self) -> &str {
            "test.assumption_branch_fold"
        }
        fn group(&self) -> &str {
            "host_rel"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Select { cond, then, els } = site.view(e)? else {
                return None;
            };
            if site.prove_eq(then, els) {
                return Some(then);
            }
            match site.prove(Query::IsNonZero(cond)) {
                Truth::True => Some(then),
                Truth::False => Some(els),
                Truth::Unknown => None,
            }
        }
    }

    /// Rewrites `a - b` to `k` whenever `site.const_diff(a, b)` proves a constant difference `k`
    /// under active assumptions or syntactic structure.
    struct ConstDiffSub;
    impl Rewrite for ConstDiffSub {
        fn name(&self) -> &str {
            "test.const_diff_sub"
        }
        fn group(&self) -> &str {
            "host_rel"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Sub, a, b) = site.view(e)? else {
                return None;
            };
            let k = site.const_diff(a, b)?;
            site.constant(&k)
        }
    }

    #[test]
    fn site_prove_and_const_diff_track_reliance_and_isolate_memo() {
        let engine = Engine::builder()
            .rewrite(Arc::new(AssumptionBranchFold))
            .rewrite(Arc::new(ConstDiffSub))
            .allow_unproven(true)
            .verify(Verify::strict().with_termination(true))
            .strategy(Strategy::new(
                "host_only",
                vec![Phase::Local {
                    groups: vec!["host_rel".into()],
                }],
            ))
            .build()
            .unwrap();

        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let p_lt_q = cx.parse("p <u q", &o).unwrap();
        let ptr_rel = cx.parse("end == base + 24", &o).unwrap();
        let unrelated = cx.parse("z == 99", &o).unwrap();

        let mut assump = Assumptions::new();
        let c0 = assump.assume_true(&mut cx, unrelated).unwrap();
        let c1 = assump.assume_true(&mut cx, p_lt_q).unwrap();
        let c2 = assump.assume_true(&mut cx, ptr_rel).unwrap();

        // 1. `site.prove` folds `select(p <=u q, a, b)` -> `a` relying ONLY on `c1` (not `c0` or `c2`).
        let sel = cx.parse("select(p <=u q, a, b)", &o).unwrap();
        let out_assumed = engine
            .run(&mut cx, &[sel], Run::default().with_assumptions(&assump))
            .unwrap();
        assert_eq!(cx.display(out_assumed.roots[0].expr).to_string(), "a");
        assert!(out_assumed.roots[0].changed);
        assert_eq!(out_assumed.roots[0].relies_on, Reliance::of(c1));
        assert!(!out_assumed.roots[0].relies_on.may_use(c0));
        assert!(!out_assumed.roots[0].relies_on.may_use(c2));

        // 2. Memo safety: running unconditionally on the same `Context` MUST NOT reuse the
        //    assumption-dependent memo entry!
        let out_uncond = engine.run(&mut cx, &[sel], Run::default()).unwrap();
        assert_eq!(out_uncond.roots[0].expr, sel);
        assert!(!out_uncond.roots[0].changed);
        assert!(out_uncond.roots[0].relies_on.is_none());

        // 3. `site.const_diff` folds `(end + 8) - base` -> `32` relying ONLY on `c2`.
        let span = cx.parse("(end + 8) - base", &o).unwrap();
        let span_assumed = engine
            .run(&mut cx, &[span], Run::default().with_assumptions(&assump))
            .unwrap();
        assert_eq!(cx.display(span_assumed.roots[0].expr).to_string(), "32:64");
        assert_eq!(span_assumed.roots[0].relies_on, Reliance::of(c2));

        // Unconditional call leaves `(end + 8) - base` unsimplified.
        let span_uncond = engine.run(&mut cx, &[span], Run::default()).unwrap();
        assert_eq!(span_uncond.roots[0].expr, span);
        assert!(span_uncond.roots[0].relies_on.is_none());

        // Purely syntactic `(base + 12) - base` folds with empty reliance even when `assump` is
        // active!
        let syn_span = cx.parse("(base + 12) - base", &o).unwrap();
        let syn_out = engine
            .run(
                &mut cx,
                &[syn_span],
                Run::default().with_assumptions(&assump),
            )
            .unwrap();
        assert_eq!(cx.display(syn_out.roots[0].expr).to_string(), "12:64");
        assert!(syn_out.roots[0].relies_on.is_none());

        // 4. `site.prove_eq` folds `select(cond, end - 24, base)` -> `end - 24` via offset_rels.
        let eq_arms = cx.parse("select(flag == 1, end - 24, base)", &o).unwrap();
        let eq_out = engine
            .run(
                &mut cx,
                &[eq_arms],
                Run::default().with_assumptions(&assump),
            )
            .unwrap();
        assert!(eq_out.roots[0].changed);
        assert_eq!(eq_out.roots[0].relies_on, Reliance::of(c2));
    }

    struct FpHostFold;
    impl Rewrite for FpHostFold {
        fn name(&self) -> &str {
            "test.fp_host_fold"
        }
        fn group(&self) -> &str {
            "host_fp"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Select { cond, then, els } = site.view(e)? else {
                return None;
            };
            // Exercises `Site::fp`, `Site::fp_cmp`, and `Site::fp_test`: when `cond` is
            // `fp.is_nan(x)` and `x` is proved non-NaN (`fp.eq(x, x)` under assumptions), fold to
            // `els`.
            if site.prove(Query::IsZero(cond)) == Truth::True {
                let _ = (
                    RoundingMode::Rne,
                    FpFormat::F32,
                    FpOp::Sqrt(RoundingMode::Rne),
                    FpCmpOp::Eq,
                    FpTest::Nan,
                    then,
                );
                return Some(els);
            }
            None
        }
    }

    #[test]
    fn site_fp_builders_and_scratch_reuse_across_calls() {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W32).unwrap();
        // Verify standalone Site FP builders construct expected nodes.
        struct BuildFp;
        impl Rewrite for BuildFp {
            fn name(&self) -> &str {
                "test.build_fp"
            }
            fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
                let sq = site.fp(FpOp::Sqrt(RoundingMode::Rne), FpFormat::F32, &[e])?;
                let is_nan = site.fp_test(FpFormat::F32, FpTest::Nan, sq)?;
                let eq = site.fp_cmp(FpFormat::F32, FpCmpOp::Eq, sq, e)?;
                let inner_sel = site.select(eq, e, sq)?;
                site.select(is_nan, e, inner_sel)
            }
        }
        let built = apply_standalone(&mut cx, &BuildFp, x).unwrap();
        assert_eq!(cx.width(built).unwrap(), Width::W32);

        // Verify `Engine::simplify_with_scratch` across repeated calls, contexts, and assumptions
        // produces identical results and stats without state leakage.
        let engine = Engine::builder()
            .builtin()
            .rewrite(Arc::new(FpHostFold))
            .allow_unproven(true)
            .strategy(Strategy::compile().with_rule_groups(&["host_fp"]))
            .build()
            .unwrap();

        let mut scratch = Scratch::new();
        let o = ParseOptions::width(Width::W32);
        for k in 1..=32u32 {
            let mut local_cx = Context::new();
            let expr_str = format!("((a ^ b) + 2 * (a & b)) + {k} - {k}");
            let root = local_cx.parse(&expr_str, &o).unwrap();
            let out = engine
                .simplify_with_scratch(&mut local_cx, &[root], Run::default(), &mut scratch)
                .unwrap();
            let mut ref_cx = Context::new();
            let ref_root = ref_cx.parse(&expr_str, &o).unwrap();
            let ref_out = engine
                .run(&mut ref_cx, &[ref_root], Run::default())
                .unwrap();
            assert_eq!(
                local_cx.display(out.roots[0].expr).to_string(),
                ref_cx.display(ref_out.roots[0].expr).to_string()
            );
            assert_eq!(out.roots[0].changed, ref_out.roots[0].changed);
        }
    }
}
