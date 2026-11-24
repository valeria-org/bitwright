//! Last-resort proofs for small word-equality residuals. All attempts operate on
//! the counterexample: a zero word means that no input can realize it.
use super::{Config, Context, Engine, Expr, Outcome, Result, prove, reduce};
use bitwright::{BinOp, Bounded, CmpOp, View};

fn zero(cx: &Context, e: Expr) -> Result<bool> {
    Ok(cx.as_const(e)?.is_some_and(|v| v.is_zero()))
}

/// Rebase `(x << k) + c` as `y << k`, where `y = x + (c >> k)`.
/// Besides the sum itself, replace both of its operands' variable parts in
/// *every* use: masks of the shifted sum and affine terms in `x` can then
/// cancel in one basis. When `x` is a subterm rather than an input this forgets
/// its definition; a proof for all `y` is still a proof for the original term.
fn rebase(cx: &mut Context, engine: &Engine, bad: Expr, nodes: &[Expr]) -> Result<bool> {
    let mut attempts = 0;
    for &sum in nodes {
        let View::Bin(BinOp::Add, shifted, offset) = cx.view(sum)? else { continue };
        let View::Bin(BinOp::Shl, x, count) = cx.view(shifted)? else { continue };
        let Some(k) = cx.as_const(count)?.and_then(|v| v.to_u64()) else { continue };
        let Some(c) = cx.as_const(offset)?.and_then(|v| v.to_u64()) else { continue };
        let w = cx.width(x)?;
        if w.bits() > 64 || k == 0 || k >= u64::from(w.bits()) || c.trailing_zeros() < k as u32 {
            continue;
        }
        let y = cx.fresh_symbol(w)?;
        let bias = cx.constant_u64(w, c >> k)?;
        let original = cx.sub(y, bias)?;
        let rebased = cx.shl(y, count)?;
        let unshifted_offset = cx.sub(rebased, offset)?;
        let candidate = cx.substitute(&[bad], &[(sum, rebased), (shifted, unshifted_offset), (x, original)])?[0];
        let result = reduce(cx, engine, candidate, 1 << 20, 3)?;
        if zero(cx, result)? { return Ok(true); }
        attempts += 1;
        if attempts == 4 { break; }
    }
    Ok(false)
}

pub(super) fn proved(cx: &mut Context, engine: &Engine, bad: Expr) -> Result<bool> {
    let View::Cmp(CmpOp::Ne, left, right) = cx.view(bad)? else { return Ok(false) };
    if !matches!(cx.dag_size(&[bad], 256)?, Bounded::Exact(_)) { return Ok(false); }
    let nodes = cx.post_order(&[bad])?;
    if rebase(cx, engine, bad, &nodes)? { return Ok(true); }

    // Prove a selector equal to a branch locally, before its value feeds
    // products or rotates on either side of the larger comparison.
    let local = Config::default().with_max_nodes(200_000).with_max_propagations(600_000);
    let mut replacements = Vec::new();
    let mut selects = 0;
    for &e in &nodes {
        if let View::Select { then, els, .. } = cx.view(e)? {
            for branch in [els, then] {
                if matches!(prove::equal(cx, e, branch, &local)?, Outcome::Proved(_)) {
                    replacements.push((e, branch));
                    break;
                }
            }
            selects += 1;
            if selects == 4 { break; }
        }
    }
    let reduced = if replacements.is_empty() { bad } else { cx.substitute(&[bad], &replacements)?[0] };
    let reduced = reduce(cx, engine, reduced, 1 << 22, 3)?;
    if zero(cx, reduced)? { return Ok(true); }
    if let View::Cmp(CmpOp::Ne, a, b) = cx.view(reduced)? {
        // A modular difference puts terms from *both* sides in the same MBA
        // normal-form query, rather than asking SAT to rediscover cancellation.
        let difference = cx.sub(a, b)?;
        let difference = reduce(cx, engine, difference, 1 << 22, 3)?;
        if zero(cx, difference)? { return Ok(true); }
    }
    // For an observed slice, normalize shared partial sums and carries below
    // the extract before blasting. Do not spend a new search on plain equalities.
    if matches!(cx.view(left)?, View::Extract { .. }) || matches!(cx.view(right)?, View::Extract { .. }) {
        let valid = cx.not(bad)?;
        let slices = Config::default().with_simplify(false).with_shared_sums(true)
            .with_max_nodes(200_000).with_max_propagations(10_000_000);
        return Ok(matches!(prove::valid(cx, valid, &slices)?, Outcome::Proved(_)));
    }
    Ok(false)
}
