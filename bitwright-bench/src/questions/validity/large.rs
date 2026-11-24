//! Last resort for a counterexample whose bit blast still exceeds the node cap.
use super::{Answer, Ask, Config, Context, Expr, Outcome, Result, Retry, Session, Split, batch, prove, reduce};

pub(super) fn recover(cx: &mut Context, checks: &[Expr], engines: &Retry) -> Result<Option<(Outcome, &'static str)>> {
    // Give the splitter the entire implication: selectors in assumptions can
    // participate in cuts just like selectors in the conclusion.
    let mut goal = checks[0];
    for &pred in &checks[1..] {
        let unless = cx.not(pred)?;
        goal = cx.or(goal, unless)?;
    }
    let cfg = Config::default().with_word_sampling(true).with_simplify_fuel(1 << 17)
        .with_max_nodes(200_000).with_max_conflicts(2_000).with_max_propagations(20_000);
    let session = Session::with_simplifiers(
        batch::Config::default().with_threads(1).with_prove(cfg).with_split(Split::shared()),
        prove::Simplifiers::new().with_mba(engines.forms),
    );
    match session.run(cx, &[Ask::valid(goal)])?.pop().ok_or("missing split answer")?.answer {
        Answer::Proved => return Ok(Some((Outcome::Proved(None), "large-split"))),
        Answer::Refuted(model) => return Ok(Some((Outcome::Refuted(model), "large-split"))),
        Answer::Unknown(_) => {}
        _ => return Err("unexpected split answer".into()),
    }

    // Discard intermediates from earlier attempts. Preserve the input DAG's
    // relative creation order (also the tie-breaker for commutative operands).
    let mut nodes = cx.post_order(checks)?;
    nodes.sort_unstable_by_key(|e| e.index());
    let offset = nodes.len();
    nodes.extend_from_slice(checks);
    let mut fresh = Context::new();
    let imported = fresh.import(cx, &nodes)?;
    let roots = &imported[offset..];
    let mut bad = fresh.not(roots[0])?;
    for &p in &roots[1..] { bad = fresh.and(bad, p)?; }
    let cold = Retry::new()?;
    for (fuel, rounds) in [(1 << 19, 3), (1 << 22, 2), (1 << 24, 1)] {
        bad = reduce(&mut fresh, &cold.word, bad, fuel, rounds)?;
        if fresh.as_const(bad)?.is_some_and(|v| v.is_zero()) {
            return Ok(Some((Outcome::Proved(None), "large-forms")));
        }
    }
    Ok(None)
}
