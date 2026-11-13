//! Batches of questions (`bitwright::batch`): answers and costs that depend on the question
//! alone, sound substitution of what was proved, and cancellation.
#![cfg(all(feature = "prove", feature = "mba"))]

use std::time::{Duration, Instant};

use bitwright::batch::{Answer, Ask, Cancel, Config, Cost, Reply, Session, Source, Split};
use bitwright::engine::Run;
use bitwright::prove::{self, Simplifiers};
use bitwright::{
    Assumptions, BitVec, Context, Expr, Facts, FnEnv, ParseOptions, PrintOptions, SymbolKey, Width,
};

fn w64() -> ParseOptions {
    ParseOptions::width(Width::W64)
}

/// A block of noise that is 0 at every `x` and `y`: no engine rule sees it at once.
const NOISE: &str = "((x ^ y) + 2 * (x & y) - x - y)";
/// Another, over other symbols.
const NOISE2: &str = "((p | q) + (p & q) - p - q)";

/// Questions that share structure: constants hidden in noise, identities, a refutable
/// claim, a question that varies, one under an assumption.
fn questions(cx: &mut Context) -> (Vec<(char, Expr, Option<Expr>)>, Expr) {
    let o = w64();
    let body = format!("0x7000 + {NOISE} * z + ({NOISE2} ^ 0x30)");
    let texts: Vec<(char, String)> = vec![
        ('c', body.clone()),
        ('c', format!("({body}) + 8")),
        ('c', format!("({body}) + 16")),
        ('c', format!("(({body}) + 24) * (1 + {NOISE})")),
        ('c', format!("x * 3 + {NOISE2}")),
        ('s', format!("({body}) + x")),
        ('s', format!("(z + {NOISE}) * 5")),
        ('v', "(x | y) + (x & y) == x + y".into()),
        ('v', "(x ^ y) + 2 * (x & y) == x + y + 1".into()),
        ('v', format!("({body}) == 0x7030")),
        ('c', "select(z <u 16, x - x + 5, 5 + 0 * y)".into()),
    ];
    let mut out = Vec::new();
    for (kind, t) in texts {
        let e = match kind {
            'v' => cx.parse(&t, &o).unwrap(),
            _ => cx.parse(&t, &o).unwrap(),
        };
        out.push((kind, e, None));
    }
    // Constant only where `z` is 3.
    let under = cx.parse(&format!("z * 2 + {NOISE}"), &o).unwrap();
    let z = cx.parse("z", &o).unwrap();
    out.push(('c', under, Some(z)));
    (out, z)
}

fn asks<'a>(qs: &[(char, Expr, Option<Expr>)], three: &'a Assumptions) -> Vec<Ask<'a>> {
    qs.iter()
        .map(|&(kind, e, assumed)| {
            let ask = match kind {
                'c' => Ask::constant(e),
                's' => Ask::simplify(e),
                _ => Ask::valid(e),
            };
            match assumed {
                Some(_) => ask.under(three),
                None => ask,
            }
        })
        .collect()
}

/// A reply as text: its answer (an expression printed, so that contexts compare) and cost.
fn shown(cx: &Context, r: &Reply) -> String {
    let answer = match &r.answer {
        Answer::Simplified { expr, end } => {
            let text = cx.display_with(*expr, PrintOptions::default().with_symbol_widths(true));
            format!("simplified {text} {end:?}")
        }
        a => format!("{a:?}"),
    };
    format!("{answer} | {:?}", r.cost)
}

/// The batch in a new context and session: every reply as text, in the order of the
/// questions whatever order they were asked in.
fn replies(config: Config, order: &dyn Fn(usize) -> Vec<usize>, runs: usize) -> Vec<String> {
    let mut cx = Context::new();
    let (qs, z) = questions(&mut cx);
    let mut three = Assumptions::new();
    let v = BitVec::from_u64(Width::W64, 3).unwrap();
    three.assume(&mut cx, z, Facts::constant(&v)).unwrap();
    let all = asks(&qs, &three);
    let order = order(all.len());
    let picked: Vec<Ask<'_>> = order.iter().map(|&k| all[k].clone()).collect();
    let session = Session::new(config);
    let mut got = Vec::new();
    for _ in 0..runs {
        got = session.run(&mut cx, &picked).unwrap();
    }
    let mut out = vec![String::new(); all.len()];
    for (&k, r) in order.iter().zip(&got) {
        out[k] = shown(&cx, r);
    }
    out
}

fn small() -> prove::Config {
    prove::Config::default()
        .with_max_conflicts(2_000)
        .with_max_nodes(200_000)
}

#[test]
fn answers_and_costs_do_not_depend_on_threads_order_or_the_store() {
    let forward = |n: usize| (0..n).collect::<Vec<_>>();
    let reverse = |n: usize| (0..n).rev().collect::<Vec<_>>();
    let rotated = |n: usize| (0..n).map(|k| (k * 5 + 3) % n).collect::<Vec<_>>();
    for split in [
        Split::default(),
        Split::eager(),
        Split::shared(),
        Split::none(),
    ] {
        let base = Config::default().with_prove(small()).with_split(split);
        let want = replies(base.with_threads(1), &forward, 1);
        // The answers, once: sound and as expected.
        assert!(want[0].starts_with("Constant(0x7030:64"), "{}", want[0]);
        assert!(want[1].starts_with("Constant(0x7038:64"), "{}", want[1]);
        assert!(want[3].starts_with("Constant(0x7048:64"), "{}", want[3]);
        assert!(want[4].starts_with("Varies"), "{}", want[4]);
        assert!(want[7].starts_with("Proved"), "{}", want[7]);
        assert!(want[8].starts_with("Refuted"), "{}", want[8]);
        assert!(want[9].starts_with("Proved"), "{}", want[9]);
        assert!(want[10].starts_with("Constant(0x5:64"), "{}", want[10]);
        assert!(want[11].starts_with("Constant(0x6:64"), "{}", want[11]);
        for threads in [1, 2, 8, 32] {
            for (name, order) in [
                ("forward", &forward as &dyn Fn(usize) -> Vec<usize>),
                ("reverse", &reverse),
                ("rotated", &rotated),
            ] {
                let got = replies(base.with_threads(threads), order, 1);
                assert_eq!(got, want, "{split:?}, {threads} threads, {name}");
            }
        }
        // Warm: everything from the store, at the cost it had.
        assert_eq!(
            replies(base.with_threads(8), &reverse, 3),
            want,
            "{split:?}, warm"
        );
        // A store that is emptied before every call.
        let tiny = base.with_threads(4).with_store_nodes(0);
        assert_eq!(replies(tiny, &rotated, 3), want, "{split:?}, emptied");
        // One question at a time, each in a session of its own.
        for (k, wanted) in want.iter().enumerate() {
            let alone = |_: usize| vec![k];
            let got = replies(base, &alone, 1);
            assert_eq!(&got[k], wanted, "{split:?}, question {k} alone");
        }
    }
}

#[test]
fn a_question_asked_whole_answers_as_the_entry_points_do() {
    let mut cx = Context::new();
    let (qs, _) = questions(&mut cx);
    let cfg = small();
    let session = Session::new(Config::default().with_prove(cfg).with_split(Split::none()));
    let simplifiers = Simplifiers::new();
    for &(kind, e, assumed) in &qs {
        if assumed.is_some() || kind == 'c' {
            continue;
        }
        // The entry point, in a context that holds the question alone.
        let mut own = Context::new();
        let root = own.import(&cx, &[e]).unwrap()[0];
        let ask = if kind == 's' {
            Ask::simplify(e)
        } else {
            Ask::valid(e)
        };
        let reply = session.run(&mut cx, &[ask]).unwrap().remove(0);
        if kind == 's' {
            let run = Run::default().with_per_call(cfg.simplify_budget);
            let out = simplifiers
                .engine(false, false)
                .run(&mut own, &[root], run)
                .unwrap();
            let want = cx.import(&own, &[out.roots[0].expr]).unwrap()[0];
            let Answer::Simplified { expr, end } = reply.answer else {
                panic!("not simplified");
            };
            assert_eq!((expr, end), (want, out.roots[0].end));
            assert_eq!(reply.cost.simplify.node_visits, out.stats.node_visits);
            assert_eq!(reply.cost.simplify.pass_work, out.stats.pass_work);
        } else {
            let mut q = prove::Question::valid_under_with(&mut own, root, None, &cfg, &simplifiers)
                .unwrap();
            let outcome = q.solve(&mut own, cfg.limits()).unwrap();
            let stats = q.stats();
            match (&reply.answer, &outcome) {
                (Answer::Proved, prove::Outcome::Proved(_)) => {}
                (Answer::Refuted(a), prove::Outcome::Refuted(b)) => assert_eq!(a, b),
                (a, b) => panic!("{a:?} against {b:?}"),
            }
            assert_eq!(reply.cost.simplify, stats.simplification.spent);
            assert_eq!(reply.cost.conflicts, stats.conflicts);
            assert_eq!(reply.cost.propagations, stats.propagations);
        }
    }
}

/// The values of `e` at an assignment that gives every symbol a value from its key.
fn value_at(cx: &mut Context, e: Expr, model: &[(SymbolKey, BitVec)]) -> BitVec {
    let env = FnEnv(|k: &SymbolKey, w: Width| {
        Some(
            model
                .iter()
                .find(|(key, _)| key == k)
                .map_or_else(|| BitVec::zero(w), |x| x.1),
        )
    });
    cx.eval(&[e], &env).unwrap()[0]
}

#[test]
fn a_hub_that_only_samples_constant_is_not_substituted() {
    let mut cx = Context::new();
    let o = w64();
    // 0 at every sample, 1 at one value of `x` that no sample is.
    let rare = "zext<64>(x * 3 == 0x123456789abcde01)";
    let e = cx.parse(&format!("0x40 + {rare} + {NOISE}"), &o).unwrap();
    for split in [Split::default(), Split::eager(), Split::shared()] {
        let session = Session::new(Config::default().with_split(split));
        let reply = session.run(&mut cx, &[Ask::constant(e)]).unwrap().remove(0);
        let Answer::Varies(models) = &reply.answer else {
            panic!("{:?}", reply.answer);
        };
        let (a, b) = (
            value_at(&mut cx, e, &models.0),
            value_at(&mut cx, e, &models.1),
        );
        assert_ne!(a, b, "the two assignments give two values");
        // As a simplification the rare case is kept too.
        let simplified = session.run(&mut cx, &[Ask::simplify(e)]).unwrap().remove(0);
        let Answer::Simplified { expr, .. } = simplified.answer else {
            panic!("not simplified");
        };
        for model in [&models.0, &models.1] {
            assert_eq!(value_at(&mut cx, expr, model), value_at(&mut cx, e, model));
        }
    }
}

#[test]
fn terms_that_cancel_across_a_chain_are_brought_together() {
    let mut cx = Context::new();
    let o = w64();
    // No operand of any `+` here is constant: the terms over `x` and `y` cancel only
    // once the terms over `z` and `w` between them are set aside.
    let text = "(x ^ y) + z * w + 2 * (x & y) + udiv(z, w | 1) + (x + y) * -1";
    let e = cx.parse(text, &o).unwrap();
    let want = cx.parse("z * w + udiv(z, w | 1)", &o).unwrap();
    let eager = Config::default().with_split(Split::eager());
    let session = Session::new(eager);
    let reply = session
        .run(&mut cx, &[Ask::equal(e, want)])
        .unwrap()
        .remove(0);
    assert_eq!(reply.answer, Answer::Proved);
    let stats = session.stats();
    assert_eq!(stats.regrouped, 1, "{stats:?}");
    assert!(stats.hubs_proved >= 1, "{stats:?}");
    // Without regrouping there is no hub to find.
    let plain = Session::new(eager.with_split(Split::eager().with_terms(false)));
    plain.run(&mut cx, &[Ask::equal(e, want)]).unwrap();
    assert_eq!(plain.stats().regrouped, 0);
}

#[test]
fn an_undecided_question_is_split_on_the_condition_its_selects_test() {
    let mut cx = Context::new();
    // Either way the condition falls, both sides are one product; a search over the
    // circuit of two multipliers behind selects does not see it within 100 conflicts.
    let text = "select(z <u 5, x * y, y + z) * select(z <u 5, y + z, x * y) == (y + z) * (x * y)";
    let p = cx.parse(text, &w64()).unwrap();
    let prove = prove::Config::default()
        .with_simplify(false)
        .with_sweeping(false)
        .with_max_conflicts(100);
    let base = Config::default().with_prove(prove);
    let whole = Session::new(base.with_split(Split::none()));
    let reply = whole.run(&mut cx, &[Ask::valid(p)]).unwrap().remove(0);
    assert!(
        matches!(reply.answer, Answer::Unknown(_)),
        "{:?}",
        reply.answer
    );
    let split = Session::new(base.with_split(Split::default().with_cases(1)));
    let reply = split.run(&mut cx, &[Ask::valid(p)]).unwrap().remove(0);
    assert_eq!(reply.answer, Answer::Proved);
    assert_eq!(split.stats().case_splits, 1);
    // A claim that is false in one case is refuted at values of that case.
    let wrong = cx
        .parse(&text.replace("== (y + z)", "== (y + z + 1)"), &w64())
        .unwrap();
    let reply = split.run(&mut cx, &[Ask::valid(wrong)]).unwrap().remove(0);
    let Answer::Refuted(model) = &reply.answer else {
        panic!("{:?}", reply.answer);
    };
    assert!(value_at(&mut cx, wrong, model).is_zero());
}

#[test]
fn from_the_bottom_a_block_of_noise_is_proved_once_for_every_hub_above_it() {
    let mut cx = Context::new();
    let o = w64();
    // Each question's constant is hidden by its own product with one shared block.
    let roots: Vec<Expr> = (0..30)
        .map(|k| {
            let t = format!(
                "{} + {NOISE} * (z + {k}) + ({NOISE2} & (w ^ {k}))",
                0x100 + k
            );
            cx.parse(&t, &o).unwrap()
        })
        .collect();
    let asks: Vec<Ask<'_>> = roots.iter().map(|&e| Ask::constant(e)).collect();
    let config = Config::default().with_threads(4);
    let top_down = Session::new(config.with_split(Split::eager()));
    let bottom_up = Session::new(config.with_split(Split::shared()));
    let a = top_down.run(&mut cx, &asks).unwrap();
    let b = bottom_up.run(&mut cx, &asks).unwrap();
    for (k, (x, y)) in a.iter().zip(&b).enumerate() {
        let want = Answer::Constant(BitVec::from_u64(Width::W64, 0x100 + k as u64).unwrap());
        assert_eq!((&x.answer, &y.answer), (&want, &want));
    }
    // From the top, every question has hubs of its own; from the bottom the two blocks
    // are asked once and what is above them folds by construction.
    let (top, bottom) = (top_down.stats(), bottom_up.stats());
    assert!(top.tasks_solved >= 30, "{top:?}");
    assert!(bottom.tasks_solved <= 4, "{bottom:?}");
}

#[test]
fn a_hub_is_proved_once_for_every_question_that_contains_it() {
    let mut cx = Context::new();
    let o = w64();
    let roots: Vec<Expr> = (0..40)
        .map(|k| {
            let t = format!("0x9000 + {k} * 8 + {NOISE} * z + ({NOISE2} ^ w)");
            cx.parse(&t, &o).unwrap()
        })
        .collect();
    let asks: Vec<Ask<'_>> = roots.iter().map(|&e| Ask::simplify(e)).collect();
    let session = Session::new(Config::default().with_split(Split::eager()).with_threads(4));
    let first = session.run(&mut cx, &asks).unwrap();
    let stats = session.stats();
    // Two hubs (the noise's product with `z`, and the other block), whatever the number
    // of questions.
    assert_eq!((stats.hubs, stats.hubs_proved), (2, 2), "{stats:?}");
    for (k, r) in first.iter().enumerate() {
        let want = cx.parse(&format!("{} + w", 0x9000 + k * 8), &o).unwrap();
        assert!(
            matches!(r.answer, Answer::Simplified { expr, .. } if expr == want),
            "{:?}",
            r.answer
        );
        assert_eq!(r.source, Source::Solved);
    }
    // Asked again: from the store, with the same costs.
    let again = session.run(&mut cx, &asks).unwrap();
    for (a, b) in first.iter().zip(&again) {
        assert_eq!((&a.answer, a.cost), (&b.answer, b.cost));
        assert_eq!(b.source, Source::Stored);
    }
    assert_eq!(session.stats().tasks_solved, stats.tasks_solved);
}

/// A question no search settles soon: a 64-bit product distributed over a sum, asked of the
/// circuit alone.
fn hard(cx: &mut Context, salt: u64) -> Expr {
    let t = format!(
        "(x + y + {salt}) * (z ^ (x >>u 7)) == x * (z ^ (x >>u 7)) + (y + {salt}) * (z ^ (x >>u 7))"
    );
    let e = cx.parse(&t, &w64());
    e.unwrap()
}

fn patient() -> Config {
    let prove = prove::Config::default()
        .with_simplify(false)
        .with_sweeping(false)
        .with_max_conflicts(u64::MAX);
    Config::default()
        .with_prove(prove)
        .with_split(Split::none())
}

#[test]
fn a_cancelled_question_stops_soon_and_says_what_it_spent() {
    let mut cx = Context::new();
    let p = hard(&mut cx, 1);
    let easy = cx.parse("x + 0 == x", &w64());
    let easy = easy.unwrap();
    let session = Session::new(patient().with_threads(2));
    let cancel = Cancel::new();
    let asks = [Ask::valid(p).cancellable(&cancel), Ask::valid(easy)];
    let (replies, late) = std::thread::scope(|s| {
        let flag = cancel.clone();
        s.spawn(move || {
            std::thread::sleep(Duration::from_millis(300));
            flag.cancel();
        });
        let t = Instant::now();
        let replies = session.run(&mut cx, &asks).unwrap();
        (replies, t.elapsed())
    });
    assert_eq!(replies[0].answer, Answer::Cancelled);
    assert!(replies[0].cost.conflicts > 0, "{:?}", replies[0].cost);
    assert_eq!(replies[1].answer, Answer::Proved);
    // Stopped within a few slices of the search, not at the end of an unbounded one.
    assert!(late < Duration::from_secs(20), "{late:?}");
    assert!(session.stats().cancelled >= 1);
    // Cancelled before it began: nothing spent, and nothing kept of it.
    let again = session.run(&mut cx, &asks[..1]).unwrap();
    assert_eq!(
        (&again[0].answer, again[0].cost),
        (&Answer::Cancelled, Cost::default())
    );
    assert_eq!(again[0].source, Source::Solved);
}

#[test]
fn cancelling_one_question_changes_no_other_answer() {
    // The same two questions, in a session where a third is cancelled under way and a
    // duplicate of the first is cancelled, and in one where nothing is.
    let run = |cancelling: bool| {
        let mut cx = Context::new();
        let (qs, z) = questions(&mut cx);
        let mut three = Assumptions::new();
        let v = BitVec::from_u64(Width::W64, 3).unwrap();
        three.assume(&mut cx, z, Facts::constant(&v)).unwrap();
        let slow = hard(&mut cx, 2);
        let prove = small().with_max_conflicts(40_000);
        let config = Config::default()
            .with_prove(prove)
            .with_split(Split::eager());
        let session = Session::new(config.with_threads(4));
        let cancel = Cancel::new();
        let mut all = asks(&qs, &three);
        let n = all.len();
        if cancelling {
            all.push(Ask::valid(slow).cancellable(&cancel));
            // The first question twice, once for someone who gives up: it is still wanted.
            all.push(all[0].clone().cancellable(&cancel));
            cancel.cancel();
        }
        let got = session.run(&mut cx, &all).unwrap();
        if cancelling {
            assert_eq!(got[n].answer, Answer::Cancelled);
            assert_eq!(
                (&got[n + 1].answer, got[n + 1].cost),
                (&got[0].answer, got[0].cost)
            );
        }
        got[..n].iter().map(|r| shown(&cx, r)).collect::<Vec<_>>()
    };
    assert_eq!(run(true), run(false));
}

#[test]
fn a_symbol_declared_otherwise_is_another_question() {
    let o = w64();
    let session = Session::new(Config::default());
    // `x & 0xff00` is 0 only when the low 16 bits are all that `x` has.
    let mut a = Context::new();
    let e = a.parse("x & 0xff0000", &o).unwrap();
    let free = session.run(&mut a, &[Ask::constant(e)]).unwrap().remove(0);
    assert!(
        matches!(free.answer, Answer::Varies(_)),
        "{:?}",
        free.answer
    );
    let mut b = Context::new();
    let x = b.parse("x", &o).unwrap();
    let high = BitVec::from_u64(Width::W64, !0xffff).unwrap();
    let known = bitwright::KnownBits::new(high, BitVec::zero(Width::W64)).unwrap();
    b.declare_known(x, known).unwrap();
    let e = b.parse("x & 0xff0000", &o).unwrap();
    let narrow = session.run(&mut b, &[Ask::constant(e)]).unwrap().remove(0);
    assert_eq!(narrow.answer, Answer::Constant(BitVec::zero(Width::W64)));
    assert_eq!(narrow.source, Source::Solved);
    assert_eq!(session.stats().flushes, 1);
}

/// `r <u 2` as the borrow of `r - 2`, in arithmetic: 0 wherever `r` is at least 2.
const BORROW: &str =
    "(((~r & 2) | ((~r | 2) & ((r ^ 0xfffffffffffffffe) + 2 * (r & 0xfffffffffffffffe)))) >>u 63)";

/// Addresses that are one constant where `r` is at least 16, as a path would know, and
/// move where it is 0 or 1; then questions under a range no random sample is in.
fn placements(cx: &mut Context) -> (Vec<Expr>, Vec<usize>, [Assumptions; 3]) {
    let o = w64();
    let bit = |v: u64| Facts::constant(&BitVec::from_u64(Width::W1, v).unwrap());
    let mut path = Assumptions::new();
    for t in ["r == 0", "r <u 0x10"] {
        let e = cx.parse(t, &o).unwrap();
        path.assume(cx, e, bit(0)).unwrap();
    }
    let mut range = Assumptions::new();
    for (t, v) in [("x == 0", 0), ("x <u 0x7ffffffeffff", 1)] {
        let e = cx.parse(t, &o).unwrap();
        range.assume(cx, e, bit(v)).unwrap();
    }
    let mut never = Assumptions::new();
    for (t, v) in [("x <u 0x10", 1), ("x <u 0x20", 0)] {
        let e = cx.parse(t, &o).unwrap();
        never.assume(cx, e, bit(v)).unwrap();
    }
    let texts = [
        // Under `path`.
        format!("0xffffcffe00000b40 + {BORROW} * (x * y + z) * 8 + {NOISE} * z"),
        format!("0xffffcffe00000b48 + (((x | {BORROW}) * z * y) ^ (x * (z * y))) + {NOISE}"),
        format!(
            "0xffffcffe00000b50 + select((x & 0xff) != 0, ((x + {BORROW}) * (y * z)) - x * y * z, (0 - {BORROW}) & (y * y * z))"
        ),
        format!("0xffffcffe00000b58 + {BORROW} * y + x"),
        // Under `range`.
        format!("7 + (x >>u 47) * (y * z) + {NOISE2}"),
        "(x >>u 46) + y".to_string(),
        // Under `never`.
        "x + 1".to_string(),
    ];
    let es = texts.iter().map(|t| cx.parse(t, &o).unwrap()).collect();
    (es, vec![0, 0, 0, 0, 1, 1, 2], [path, range, never])
}

fn placement_config() -> Config {
    let prove = small().with_max_propagations(20_000);
    Config::default()
        .with_prove(prove)
        .with_split(Split::shared())
}

/// Whether `model` satisfies the constraints `texts` (each with the value it must have).
fn satisfies(cx: &mut Context, model: &[(SymbolKey, BitVec)], texts: &[(&str, u64)]) -> bool {
    texts.iter().all(|&(t, v)| {
        let e = cx.parse(t, &w64()).unwrap();
        value_at(cx, e, model) == BitVec::from_u64(Width::W1, v).unwrap()
    })
}

#[test]
fn a_node_constant_under_the_assumptions_is_a_proof_of_its_own() {
    let mut cx = Context::new();
    let (es, _, [path, ..]) = placements(&mut cx);
    let session = Session::new(placement_config());
    let asks: Vec<Ask<'_>> = es[..4]
        .iter()
        .map(|&e| Ask::constant(e).under(&path))
        .collect();
    let got = session.run(&mut cx, &asks).unwrap();
    for (k, lane) in [0xb40u64, 0xb48, 0xb50].into_iter().enumerate() {
        let want = BitVec::from_u64(Width::W64, 0xffff_cffe_0000_0000 + lane).unwrap();
        assert_eq!(got[k].answer, Answer::Constant(want), "question {k}");
    }
    assert!(matches!(got[3].answer, Answer::Varies(_)), "{:?}", got[3]);
    let stats = session.stats();
    assert!(stats.hubs_assumed > 0, "{stats:?}");
    // What was proved under the assumptions serves no question asked without them, or
    // under others: there the addresses move.
    let mut weaker = Assumptions::new();
    let nonzero = cx.parse("r == 0", &w64()).unwrap();
    let zero = BitVec::from_u64(Width::W1, 0).unwrap();
    weaker
        .assume(&mut cx, nonzero, Facts::constant(&zero))
        .unwrap();
    for &e in &es[..3] {
        let asks = [Ask::constant(e), Ask::constant(e).under(&weaker)];
        for (reply, facts) in session
            .run(&mut cx, &asks)
            .unwrap()
            .iter()
            .zip([&[][..], &[("r == 0", 0)][..]])
        {
            match &reply.answer {
                Answer::Varies(models) => {
                    for m in [&models.0, &models.1] {
                        assert!(satisfies(&mut cx, m, facts), "{m:?}");
                    }
                    assert_ne!(
                        value_at(&mut cx, e, &models.0),
                        value_at(&mut cx, e, &models.1)
                    );
                }
                Answer::Unknown(_) => {}
                other => panic!("{other:?}"),
            }
        }
    }
    // Without such hubs the second is left to one search, which the limits stop.
    let plain = placement_config();
    let plain = plain.with_split(plain.split.with_assumed(false));
    let session = Session::new(plain);
    let reply = session.run(&mut cx, &asks[1..2]).unwrap().remove(0);
    let Answer::Unknown(prove::Unknown::Budget { propagations, .. }) = reply.answer else {
        panic!("{:?}", reply.answer);
    };
    // The limits are each proof's: what the last one did is in the answer (its search, to
    // the limit, and the sweep before it, to half the limit), what all of them did in the
    // cost.
    assert!((20_000..31_000).contains(&propagations), "{propagations}");
    assert!(reply.cost.propagations >= propagations && reply.cost.tasks > 1);
}

#[test]
fn where_no_sample_satisfies_the_assumptions_an_assignment_is_searched_for() {
    let mut cx = Context::new();
    let (es, _, [_, range, never]) = placements(&mut cx);
    let facts = [("x == 0", 0), ("x <u 0x7ffffffeffff", 1)];
    for split in [Split::default(), Split::shared(), Split::none()] {
        let session = Session::new(placement_config().with_split(split));
        let asks = [
            Ask::constant(es[4]).under(&range),
            Ask::constant(es[5]).under(&range),
            Ask::constant(es[6]).under(&never),
        ];
        let got = session.run(&mut cx, &asks).unwrap();
        let seven = BitVec::from_u64(Width::W64, 7).unwrap();
        assert_eq!(got[0].answer, Answer::Constant(seven), "{split:?}");
        // The search only chose where to read the value: the constant is proved.
        let k = cx.constant(&seven).unwrap();
        let claim = cx.cmp(bitwright::CmpOp::Eq, es[4], k).unwrap();
        let direct = prove::valid_under(&mut cx, claim, Some(&range), &prove::Config::default());
        assert!(matches!(direct.unwrap(), prove::Outcome::Proved(_)));
        let Answer::Varies(models) = &got[1].answer else {
            panic!("{split:?}: {:?}", got[1].answer);
        };
        for m in [&models.0, &models.1] {
            assert!(satisfies(&mut cx, m, &facts), "{m:?}");
        }
        assert_ne!(
            value_at(&mut cx, es[5], &models.0),
            value_at(&mut cx, es[5], &models.1)
        );
        let Answer::Unknown(prove::Unknown::Unsupported(why)) = &got[2].answer else {
            panic!("{split:?}: {:?}", got[2].answer);
        };
        assert!(why.contains("cannot hold"), "{why}");
    }
}

#[test]
fn answers_under_assumptions_do_not_depend_on_threads_order_or_the_store() {
    let run = |config: Config, order: &[usize], runs: usize, cancel_last: bool| {
        let mut cx = Context::new();
        let (es, which, facts) = placements(&mut cx);
        let cancel = Cancel::new();
        let mut asks: Vec<Ask<'_>> = order
            .iter()
            .map(|&k| Ask::constant(es[k]).under(&facts[which[k]]))
            .collect();
        if cancel_last {
            // Someone else's question over the same parts, given up before it starts.
            asks.push(Ask::constant(es[1]).under(&facts[1]).cancellable(&cancel));
            cancel.cancel();
        }
        let session = Session::new(config);
        let mut got = Vec::new();
        for _ in 0..runs {
            got = session.run(&mut cx, &asks).unwrap();
        }
        let mut out = vec![String::new(); es.len()];
        for (&k, r) in order.iter().zip(&got) {
            out[k] = shown(&cx, r);
        }
        out
    };
    let all: Vec<usize> = (0..7).collect();
    let reverse: Vec<usize> = (0..7).rev().collect();
    let rotated: Vec<usize> = (0..7).map(|k| (k * 3 + 2) % 7).collect();
    for split in [Split::default(), Split::eager(), Split::shared()] {
        let base = placement_config().with_split(split);
        let want = run(base.with_threads(1), &all, 1, false);
        for threads in [1, 2, 8, 32] {
            for order in [&all, &reverse, &rotated] {
                let got = run(base.with_threads(threads), order, 1, false);
                assert_eq!(got, want, "{split:?}, {threads} threads, {order:?}");
            }
        }
        assert_eq!(run(base.with_threads(8), &reverse, 3, false), want, "warm");
        let tiny = base.with_threads(4).with_store_nodes(0);
        assert_eq!(run(tiny, &rotated, 3, false), want, "{split:?}, emptied");
        assert_eq!(run(base.with_threads(4), &all, 1, true), want, "cancelled");
        for k in 0..7 {
            let got = run(base, &[k], 1, false);
            assert_eq!(got[k], want[k], "{split:?}, question {k} alone");
        }
        // A question whose assumptions were searched for in an earlier call costs the same.
        let mut cx = Context::new();
        let (es, which, facts) = placements(&mut cx);
        let session = Session::new(base.with_threads(2));
        for k in [4, 5] {
            let ask = Ask::constant(es[k]).under(&facts[which[k]]);
            let reply = session.run(&mut cx, &[ask]).unwrap().remove(0);
            assert_eq!(shown(&cx, &reply), want[k], "{split:?}, question {k} later");
        }
    }
}
