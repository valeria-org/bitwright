//! Checking host rewrites offline: see [`rewrite`].

use core::fmt;
use std::sync::Arc;

use super::{Rng, biased};
use crate::engine::Rewrite;
use crate::engine::host::apply_standalone;
use crate::ext::Registry;
use crate::{BitVec, Context, ContextConfig, Expr, FnEnv, ParseOptions, SymbolKey, Width};

/// How thoroughly [`rewrite`] checks.
#[derive(Clone, Debug)]
#[non_exhaustive]
pub struct RewriteCheckConfig {
    /// Widths each input is parsed at (an input whose constants do not fit a width skips it).
    pub widths: Vec<u16>,
    /// Variations of each input at each width, with other constants of the same widths.
    pub variants: u32,
    /// Compare every assignment of the symbols when they have at most this many bits.
    pub max_exhaustive_bits: u32,
    /// Random points otherwise (after all zeros and all ones).
    pub samples: u32,
    /// Seed for the variations and the points.
    pub seed: u64,
    /// The extension operations the inputs call, if any.
    pub registry: Option<Arc<Registry>>,
}

impl Default for RewriteCheckConfig {
    fn default() -> Self {
        RewriteCheckConfig {
            widths: vec![1, 2, 3, 4, 5, 6, 7, 8, 16, 32, 64],
            variants: 16,
            max_exhaustive_bits: 16,
            samples: 256,
            seed: 0x5eed_4057,
            registry: None,
        }
    }
}

setters!(RewriteCheckConfig {
    with_widths: widths: Vec<u16>,
    with_variants: variants: u32,
    with_max_exhaustive_bits: max_exhaustive_bits: u32,
    with_samples: samples: u32,
    with_seed: seed: u64,
    with_registry: registry ? Arc<Registry>,
});

/// What a passing check covered.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub struct RewriteReport {
    /// Nodes where the rewrite returned a result other than the node.
    pub applications: u64,
    /// Points at which a result was compared with its node.
    pub points: u64,
    /// Applications compared at every assignment of their symbols.
    pub exhaustive: u64,
}

/// Why a check failed. Expressions are shown in the expression syntax.
#[derive(Clone, Debug, PartialEq, Eq)]
#[non_exhaustive]
pub enum RewriteFailure {
    /// An input parses at none of the widths.
    Unparsable {
        /// The input.
        input: String,
    },
    /// The rewrite applied nowhere: the inputs do not exercise it.
    NeverApplied,
    /// A result differs from its node at an assignment.
    Differs {
        /// The node.
        node: String,
        /// The rewrite's result.
        result: String,
        /// The symbols' values.
        assignment: Vec<(String, BitVec)>,
    },
    /// A result of another width.
    Width {
        /// The node.
        node: String,
        /// The rewrite's result.
        result: String,
    },
    /// A result not smaller than its node in the termination order: the engine would never
    /// commit it.
    NotSmaller {
        /// The node.
        node: String,
        /// The rewrite's result.
        result: String,
    },
    /// The same node gave two results.
    Nondeterministic {
        /// The node.
        node: String,
        /// The first result.
        first: String,
        /// The second.
        second: String,
    },
    /// A result that is not a handle of the context the rewrite was given.
    ForeignExpr {
        /// The node.
        node: String,
    },
}

impl fmt::Display for RewriteFailure {
    fn fmt(&self, f: &mut fmt::Formatter<'_>) -> fmt::Result {
        match self {
            RewriteFailure::Unparsable { input } => {
                write!(f, "`{input}` parses at none of the widths")
            }
            RewriteFailure::NeverApplied => {
                write!(f, "the rewrite applied at no node of the inputs")
            }
            RewriteFailure::Differs {
                node,
                result,
                assignment,
            } => {
                write!(f, "`{node}` => `{result}` differs at")?;
                for (k, (name, v)) in assignment.iter().enumerate() {
                    write!(f, "{} {name} = {v}", if k == 0 { "" } else { "," })?;
                }
                Ok(())
            }
            RewriteFailure::Width { node, result } => {
                write!(f, "`{node}` => `{result}` changes the width")
            }
            RewriteFailure::NotSmaller { node, result } => write!(
                f,
                "`{node}` => `{result}` is not smaller in the termination order (never committed)"
            ),
            RewriteFailure::Nondeterministic {
                node,
                first,
                second,
            } => write!(f, "`{node}` gave `{first}` and then `{second}`"),
            RewriteFailure::ForeignExpr { node } => {
                write!(
                    f,
                    "at `{node}` the rewrite returned a handle of another context"
                )
            }
        }
    }
}

impl std::error::Error for RewriteFailure {}

/// Checks host rewrite `r` on `inputs` (text in the expression syntax): a report of what was
/// covered, or the first failure found. The evidence a host gathers in its own test suite
/// before it links the rewrite with
/// [`EngineBuilder::trusted_rewrite`](crate::engine::EngineBuilder::trusted_rewrite).
///
/// Arbitrary code cannot be proved the way a `.bwr` rule is, so the checker tests it where it
/// applies:
/// - at every node of every input, at every width the input parses at, and on variations of
///   it with other constants;
/// - each result compared with its node at every assignment of their symbols when those have
///   few bits, and at boundary-biased random points otherwise;
/// - what the engine relies on: the result has the node's width, the same node gives the
///   same result, and the result is smaller in the termination order (else the engine never
///   commits it).
///
/// This is testing, not proof, and it covers only the shapes the inputs exercise: give inputs
/// where the rewrite applies and where it nearly does.
///
/// ```
/// use bitwright::check::{RewriteCheckConfig, RewriteFailure, rewrite};
/// use bitwright::engine::{Rewrite, Site};
/// use bitwright::{BinOp, Expr, View};
///
/// /// `(x ^ c) ^ c` as `x`: right.
/// struct XorTwice;
/// impl Rewrite for XorTwice {
///     fn name(&self) -> &str { "acme.xor_twice" }
///     fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
///         let View::Bin(BinOp::Xor, a, c) = site.view(e)? else { return None };
///         let View::Bin(BinOp::Xor, x, d) = site.view(a)? else { return None };
///         (c == d).then_some(x)
///     }
/// }
/// let report = rewrite(&XorTwice, &["(x ^ 5) ^ 5", "((y + z) ^ 12) ^ 12"], &RewriteCheckConfig::default())?;
/// assert!(report.applications > 0);
///
/// /// `(x + c) - c` as `x + c`: wrong.
/// struct Wrong;
/// impl Rewrite for Wrong {
///     fn name(&self) -> &str { "acme.wrong" }
///     fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
///         let View::Bin(BinOp::Add, a, _) = site.view(e)? else { return None };
///         matches!(site.view(a)?, View::Bin(BinOp::Add, ..)).then_some(a)
///     }
/// }
/// let failure = rewrite(&Wrong, &["(x + 3) - 3"], &RewriteCheckConfig::default()).unwrap_err();
/// assert!(matches!(failure, RewriteFailure::Differs { .. }));
/// # Ok::<(), Box<dyn std::error::Error>>(())
/// ```
pub fn rewrite(
    r: &dyn Rewrite,
    inputs: &[&str],
    cfg: &RewriteCheckConfig,
) -> Result<RewriteReport, RewriteFailure> {
    let mut report = RewriteReport {
        applications: 0,
        points: 0,
        exhaustive: 0,
    };
    let mut rng = Rng(cfg.seed);
    for input in inputs {
        let mut parsed = false;
        for &bits in &cfg.widths {
            let Ok(w) = Width::new(bits) else {
                continue;
            };
            let mut cx = match &cfg.registry {
                Some(reg) => Context::with_registry(ContextConfig::default(), reg.clone()),
                None => Context::new(),
            };
            let Ok(root) = cx.parse(input, &ParseOptions::width(w)) else {
                continue;
            };
            parsed = true;
            let mut roots = vec![root];
            roots.extend(variants(&mut cx, root, cfg.variants, &mut rng));
            for root in roots {
                check_root(&mut cx, r, root, cfg, &mut rng, &mut report)?;
            }
        }
        if !parsed {
            return Err(RewriteFailure::Unparsable {
                input: (*input).to_string(),
            });
        }
    }
    if report.applications == 0 {
        return Err(RewriteFailure::NeverApplied);
    }
    Ok(report)
}

/// `root` with other constants: each distinct constant replaced by a boundary-biased value of
/// its width (rebuilt through the builder, so folded where it folds).
fn variants(cx: &mut Context, root: Expr, n: u32, rng: &mut Rng) -> Vec<Expr> {
    let Ok(order) = cx.post_order(&[root]) else {
        return Vec::new();
    };
    let consts: Vec<(Expr, Width)> = order
        .into_iter()
        .filter_map(|e| cx.as_const(e).ok().flatten().map(|v| (e, v.width())))
        .collect();
    if consts.is_empty() {
        return Vec::new();
    }
    (0..n)
        .filter_map(|_| {
            let map: Vec<(Expr, Expr)> = consts
                .iter()
                .filter_map(|&(e, w)| Some((e, cx.constant(&biased(rng, w)).ok()?)))
                .collect();
            cx.substitute(&[root], &map).ok().map(|r| r[0])
        })
        .collect()
}

/// Applies `r` at every node of `root`'s DAG and checks every result.
fn check_root(
    cx: &mut Context,
    r: &dyn Rewrite,
    root: Expr,
    cfg: &RewriteCheckConfig,
    rng: &mut Rng,
    report: &mut RewriteReport,
) -> Result<(), RewriteFailure> {
    let Ok(order) = cx.post_order(&[root]) else {
        return Ok(());
    };
    for n in order {
        let Some(out) = apply_standalone(cx, r, n) else {
            continue;
        };
        let show = |cx: &Context, e: Expr| cx.display(e).to_string();
        let (Ok(ni), Ok(oi)) = (cx.id(n), cx.id(out)) else {
            return Err(RewriteFailure::ForeignExpr { node: show(cx, n) });
        };
        if ni == oi {
            continue;
        }
        if cx.width(n).ok() != cx.width(out).ok() {
            return Err(RewriteFailure::Width {
                node: show(cx, n),
                result: show(cx, out),
            });
        }
        if let Some(again) = apply_standalone(cx, r, n).filter(|&a| a != out) {
            return Err(RewriteFailure::Nondeterministic {
                node: show(cx, n),
                first: show(cx, out),
                second: show(cx, again),
            });
        }
        if crate::rules::order::ground_greater(cx, ni, oi) != Some(true) {
            return Err(RewriteFailure::NotSmaller {
                node: show(cx, n),
                result: show(cx, out),
            });
        }
        compare(cx, n, out, cfg, rng, report)?;
        report.applications += 1;
    }
    Ok(())
}

/// Compares `a` and `b` at every assignment of their symbols, or at sampled ones.
fn compare(
    cx: &mut Context,
    a: Expr,
    b: Expr,
    cfg: &RewriteCheckConfig,
    rng: &mut Rng,
    report: &mut RewriteReport,
) -> Result<(), RewriteFailure> {
    let syms = cx.symbols_in(&[a, b]).unwrap_or_default();
    let keys: Vec<(SymbolKey, Width)> = syms
        .iter()
        .filter_map(|&s| Some((cx.symbol_key(s)?.clone(), cx.symbol_width(s)?)))
        .collect();
    let bits: u32 = keys.iter().map(|(_, w)| u32::from(w.bits())).sum();
    let exhaustive = bits <= cfg.max_exhaustive_bits.min(24);
    let cases: u64 = if exhaustive {
        1 << bits
    } else {
        2 + u64::from(cfg.samples)
    };
    for case in 0..cases {
        let mut rest = case;
        let vals: Vec<(SymbolKey, BitVec)> = keys
            .iter()
            .map(|(k, w)| {
                let v = if exhaustive {
                    let v = rest & ((1u64 << w.bits()) - 1);
                    rest >>= w.bits();
                    BitVec::wrapping_from_u64(*w, v)
                } else {
                    match case {
                        0 => BitVec::zero(*w),
                        1 => BitVec::ones(*w),
                        _ => biased(rng, *w),
                    }
                };
                (k.clone(), v)
            })
            .collect();
        let env = FnEnv(|k: &SymbolKey, _| vals.iter().find(|(kk, _)| kk == k).map(|(_, v)| *v));
        let Ok(r) = cx.eval(&[a, b], &env) else {
            continue;
        };
        report.points += 1;
        if r[0] != r[1] {
            return Err(RewriteFailure::Differs {
                node: cx.display(a).to_string(),
                result: cx.display(b).to_string(),
                assignment: vals.into_iter().map(|(k, v)| (k.to_string(), v)).collect(),
            });
        }
    }
    if exhaustive {
        report.exhaustive += 1;
    }
    Ok(())
}

#[cfg(test)]
mod tests {
    use super::*;
    use crate::engine::Site;
    use crate::{BinOp, View};
    use std::sync::atomic::{AtomicU64, Ordering};

    fn cfg() -> RewriteCheckConfig {
        RewriteCheckConfig::default().with_widths(vec![4, 8, 64])
    }

    /// `x << k => x * 2^k`: right, but larger in the order.
    struct ShlToMul;
    impl Rewrite for ShlToMul {
        fn name(&self) -> &str {
            "t.shl_to_mul"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Shl, x, k) = site.view(e)? else {
                return None;
            };
            let m = 1u64.checked_shl(u32::try_from(site.as_u64(k)?).ok()?)?;
            let w = site.width(e)?;
            let m = site.constant_u64(w, m & (u64::MAX >> (64 - w.bits())))?;
            site.bin(BinOp::Mul, x, m)
        }
    }

    /// `x + y => trunc(x)`: another width.
    struct Narrows;
    impl Rewrite for Narrows {
        fn name(&self) -> &str {
            "t.narrows"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Add, x, _) = site.view(e)? else {
                return None;
            };
            site.trunc(x, Width::W1)
        }
    }

    /// `x + y` to `x`, then to `y`, alternately: not a function of the node.
    struct Flaky(AtomicU64);
    impl Rewrite for Flaky {
        fn name(&self) -> &str {
            "t.flaky"
        }
        fn rewrite(&self, site: &mut Site<'_>, e: Expr) -> Option<Expr> {
            let View::Bin(BinOp::Add, x, y) = site.view(e)? else {
                return None;
            };
            let k = self.0.fetch_add(1, Ordering::Relaxed);
            Some(if k.is_multiple_of(2) { x } else { y })
        }
    }

    #[test]
    fn failures_are_reported() {
        assert!(matches!(
            rewrite(&ShlToMul, &["x << 3"], &cfg()),
            Err(RewriteFailure::NotSmaller { node, .. }) if node == "x << 3"
        ));
        assert!(matches!(
            rewrite(&Narrows, &["x + y"], &cfg()),
            Err(RewriteFailure::Width { .. })
        ));
        assert!(matches!(
            rewrite(&Flaky(AtomicU64::new(0)), &["x + y"], &cfg()),
            Err(RewriteFailure::Nondeterministic { .. })
        ));
        assert_eq!(
            rewrite(&ShlToMul, &["x + y"], &cfg()),
            Err(RewriteFailure::NeverApplied)
        );
        assert!(matches!(
            rewrite(&ShlToMul, &["x +"], &cfg()),
            Err(RewriteFailure::Unparsable { .. })
        ));
    }
}
