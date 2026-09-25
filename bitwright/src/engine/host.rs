//! Rewrites a host defines in Rust: see [`Rewrite`].

use core::fmt;

use super::budget::Counter;
use super::{Accept, By, Fin, Reject, Runner, Step, Stop};
use crate::error::Error;
use crate::expr::{Context, Expr, View};
use crate::facts::{Facts, KnownBits};
use crate::ops::{BinOp, CmpOpExt, UnOp};
use crate::{BitVec, Width};

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

/// The engine side of a [`Site`]: construction as engine work, and facts under the call's
/// budget and assumptions.
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
