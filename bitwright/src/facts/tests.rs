//! Fact soundness: every transfer, the reduced product, context-level facts and proofs.

use std::collections::HashMap;

use super::transfer::{TOp, transfer};
use super::*;
use crate::testutil::{Gen, Rng, width};
use crate::{BinOp, CmpOpExt, SymbolKey, UnOp};

fn all_values(w: u16) -> Vec<BitVec> {
    (0..(1u64 << w))
        .map(|v| BitVec::wrapping_from_u64(width(w), v))
        .collect()
}

/// The tightest facts describing a non-empty set of values (sound for that set).
fn facts_of_set(vals: &[BitVec]) -> Facts {
    let w = vals[0].width();
    let mut f = Facts::constant(&vals[0]);
    for v in &vals[1..] {
        f = f.hull(&Facts::constant(v));
    }
    assert_eq!(f.width(), w);
    f
}

/// Input fact states at width `w`: every known-bits pattern, facts of random subsets, and
/// random unsigned and signed intervals.
fn states(rng: &mut Rng, w: u16, random: usize) -> Vec<Facts> {
    let vals = all_values(w);
    let mut out = Vec::new();
    if w <= 3 {
        // Every KnownBits: each bit is 0, 1 or unknown.
        let n = 3u64.pow(u32::from(w));
        for code in 0..n {
            let (mut z, mut o, mut c) = (0u64, 0u64, code);
            for b in 0..w {
                match c % 3 {
                    0 => z |= 1 << b,
                    1 => o |= 1 << b,
                    _ => {}
                }
                c /= 3;
            }
            let k = KnownBits::new(
                BitVec::wrapping_from_u64(width(w), z),
                BitVec::wrapping_from_u64(width(w), o),
            )
            .unwrap();
            out.push(Facts::from_known(k));
        }
    }
    for _ in 0..random {
        match rng.below(3) {
            0 => {
                let subset: Vec<BitVec> =
                    vals.iter().filter(|_| rng.chance(1, 3)).copied().collect();
                if !subset.is_empty() {
                    out.push(facts_of_set(&subset));
                }
            }
            1 => {
                let (a, b) = (rng.below(1 << w), rng.below(1 << w));
                let (lo, hi) = (a.min(b), a.max(b));
                let u = URange::new(
                    BitVec::wrapping_from_u64(width(w), lo),
                    BitVec::wrapping_from_u64(width(w), hi),
                )
                .unwrap();
                if let Some(f) =
                    Facts::reduce(KnownBits::unknown(width(w)), u, SRange::full(width(w)))
                {
                    out.push(f);
                }
            }
            _ => {
                let (a, b) = (
                    BitVec::wrapping_from_u64(width(w), rng.below(1 << w)),
                    BitVec::wrapping_from_u64(width(w), rng.below(1 << w)),
                );
                let (lo, hi) = if sle(&a, &b) { (a, b) } else { (b, a) };
                let s = SRange::new(lo, hi).unwrap();
                if let Some(f) =
                    Facts::reduce(KnownBits::unknown(width(w)), URange::full(width(w)), s)
                {
                    out.push(f);
                }
            }
        }
    }
    out
}

fn members(f: &Facts) -> Vec<BitVec> {
    all_values(f.width().bits())
        .into_iter()
        .filter(|v| f.contains(v))
        .collect()
}

fn eval_top(op: &TOp, args: &[BitVec]) -> BitVec {
    match *op {
        TOp::Un(u) => BitVec::apply_un(u, &args[0]).unwrap(),
        TOp::Bin(b) => BitVec::apply_bin(b, &args[0], &args[1]).unwrap(),
        TOp::Cmp(c) => BitVec::from_bool(BitVec::apply_cmp(c, &args[0], &args[1]).unwrap()),
        TOp::Zext(to) => args[0].zext(to).unwrap(),
        TOp::Sext(to) => args[0].sext(to).unwrap(),
        TOp::Extract { lo, width } => args[0].extract(lo, width).unwrap(),
        TOp::Concat => BitVec::concat(&args[0], &args[1]).unwrap(),
        TOp::Select => BitVec::select(&args[0], &args[1], &args[2]).unwrap(),
        TOp::Const(v) => v,
        TOp::Top(_) => unreachable!(),
    }
}

fn check_sound(op: &TOp, ins: &[&Facts]) {
    let out = transfer(op, ins);
    let sets: Vec<Vec<BitVec>> = ins.iter().map(|f| members(f)).collect();
    if sets.iter().any(|s| s.is_empty()) {
        return;
    }
    let mut idx = vec![0usize; sets.len()];
    loop {
        let args: Vec<BitVec> = idx.iter().zip(&sets).map(|(&i, s)| s[i]).collect();
        let v = eval_top(op, &args);
        assert!(
            out.contains(&v),
            "{op:?} unsound: inputs {ins:?} values {args:?} -> {v} not in {out:?}"
        );
        // Next tuple.
        let mut k = 0;
        loop {
            if k == idx.len() {
                return;
            }
            idx[k] += 1;
            if idx[k] < sets[k].len() {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

#[test]
fn every_transfer_is_sound_exhaustively() {
    let mut rng = Rng(0xfac7_0001);
    for w in 1..=3u16 {
        let st = states(&mut rng, w, 30);
        let ww = width(w);
        for a in &st {
            for op in UnOp::ALL {
                if op == UnOp::Bswap && !w.is_multiple_of(8) {
                    continue;
                }
                check_sound(&TOp::Un(op), &[a]);
            }
            for to in (w + 1)..=(w + 2) {
                check_sound(&TOp::Zext(width(to)), &[a]);
                check_sound(&TOp::Sext(width(to)), &[a]);
            }
            for lo in 0..w {
                for len in 1..=(w - lo) {
                    check_sound(
                        &TOp::Extract {
                            lo,
                            width: width(len),
                        },
                        &[a],
                    );
                }
            }
            for b in &st {
                for op in BinOp::ALL {
                    check_sound(&TOp::Bin(op), &[a, b]);
                }
                for op in CmpOp::ALL {
                    check_sound(&TOp::Cmp(op), &[a, b]);
                }
            }
        }
        // Concatenation and select with states of other widths.
        let ones = states(&mut rng, 1, 0);
        let st2 = states(&mut rng, 2, 10);
        for a in &st {
            for b in &st2 {
                check_sound(&TOp::Concat, &[a, b]);
                check_sound(&TOp::Concat, &[b, a]);
            }
            for c in &ones {
                for b in st.iter().take(12) {
                    check_sound(&TOp::Select, &[c, a, b]);
                }
            }
        }
        let _ = ww;
    }
}

#[test]
fn transfers_are_sound_on_sampled_states() {
    let mut rng = Rng(0xfac7_0002);
    for w in [4u16, 5, 6, 8] {
        let st = states(&mut rng, w, 40);
        for _ in 0..1500 {
            let a = &st[rng.below(st.len() as u64) as usize];
            let b = &st[rng.below(st.len() as u64) as usize];
            let op = BinOp::ALL[rng.below(19) as usize];
            check_sound(&TOp::Bin(op), &[a, b]);
            let u = UnOp::ALL[rng.below(7) as usize];
            if u != UnOp::Bswap || w.is_multiple_of(8) {
                check_sound(&TOp::Un(u), &[a]);
            }
            check_sound(&TOp::Cmp(CmpOp::ALL[rng.below(6) as usize]), &[a, b]);
        }
    }
}

#[test]
fn transfers_are_sound_at_wide_widths() {
    // Facts from random sets of wide values; check those same values (a sample of each
    // concretization, which is all that can be enumerated at this width).
    let mut rng = Rng(0xfac7_0003);
    for w in [63u16, 64, 65, 127, 128, 129, 200, 512] {
        let ww = width(w);
        for _ in 0..60 {
            let mut set_a = Vec::new();
            let mut set_b = Vec::new();
            let base: Vec<u64> = (0..8).map(|_| rng.next()).collect();
            for _ in 0..4 {
                let mut l = base.clone();
                l[rng.below(8) as usize] ^= 1 << rng.below(64);
                set_a.push(BitVec::wrapping_from_limbs(ww, &l));
                set_b.push(BitVec::wrapping_from_u64(ww, rng.below(u64::from(w) + 3)));
            }
            let (fa, fb) = (facts_of_set(&set_a), facts_of_set(&set_b));
            for op in BinOp::ALL {
                let out = transfer(&TOp::Bin(op), &[&fa, &fb]);
                for a in &set_a {
                    for b in &set_b {
                        let v = BitVec::apply_bin(op, a, b).unwrap();
                        assert!(
                            out.contains(&v),
                            "{op:?} at {w}: {a} {b} -> {v} not in {out:?}"
                        );
                    }
                }
            }
            for op in UnOp::ALL {
                if op == UnOp::Bswap && !w.is_multiple_of(8) {
                    continue;
                }
                let out = transfer(&TOp::Un(op), &[&fa]);
                for a in &set_a {
                    let v = BitVec::apply_un(op, a).unwrap();
                    assert!(out.contains(&v), "{op:?} at {w}: {a} -> {v} not in {out:?}");
                }
            }
        }
    }
}

#[test]
fn reduced_product_keeps_every_common_member() {
    let mut rng = Rng(0xfac7_0004);
    for w in 1..=5u16 {
        let ww = width(w);
        let vals = all_values(w);
        for _ in 0..400 {
            let st = states(&mut rng, w, 3);
            let k = st[rng.below(st.len() as u64) as usize].known;
            let (a, b) = (rng.below(1 << w), rng.below(1 << w));
            let u = URange::new(
                BitVec::wrapping_from_u64(ww, a.min(b)),
                BitVec::wrapping_from_u64(ww, a.max(b)),
            )
            .unwrap();
            let (c, d) = (
                BitVec::wrapping_from_u64(ww, rng.below(1 << w)),
                BitVec::wrapping_from_u64(ww, rng.below(1 << w)),
            );
            let s = if sle(&c, &d) {
                SRange::new(c, d)
            } else {
                SRange::new(d, c)
            }
            .unwrap();
            let common: Vec<&BitVec> = vals
                .iter()
                .filter(|v| k.contains(v) && u.contains(v) && s.contains(v))
                .collect();
            match Facts::reduce(k, u, s) {
                None => assert!(common.is_empty(), "reduce lost members {common:?}"),
                Some(f) => {
                    for v in common {
                        assert!(f.contains(v), "reduce dropped {v}");
                    }
                }
            }
        }
    }
}

// ----- context-level facts and proofs ---------------------------------------------------------

fn random_env(g: &mut Gen) -> HashMap<SymbolKey, BitVec> {
    g.vars
        .clone()
        .into_iter()
        .map(|(n, w)| {
            let limbs: Vec<u64> = (0..3).map(|_| g.rng.next()).collect();
            (
                SymbolKey::from(n.as_str()),
                BitVec::wrapping_from_limbs(width(w), &limbs),
            )
        })
        .collect()
}

#[test]
fn context_facts_contain_every_evaluation() {
    for seed in 0..300u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xfac7_1000 + seed),
            max_w: if seed % 3 == 0 { 70 } else { 8 },
            vars: Vec::new(),
        };
        let w = 1 + g.rng.below(u64::from(g.max_w)) as u16;
        let (e, _) = g.expr(&mut cx, w, 5);
        let all = cx.post_order(&[e]).unwrap();
        let facts: Vec<Facts> = all.iter().map(|&x| cx.facts(x).unwrap()).collect();
        for _ in 0..24 {
            let env = random_env(&mut g);
            let vals = cx.eval(&all, &env).unwrap();
            for ((x, f), v) in all.iter().zip(&facts).zip(&vals) {
                assert!(f.contains(v), "{}: {v} not in {f:?}", cx.display(*x));
            }
        }
    }
}

/// A concrete check of a query's claim on the values of `a` and `b`.
type Holds = Box<dyn Fn(&BitVec, &BitVec) -> bool>;

#[test]
fn proofs_are_sound() {
    let mut proved = 0;
    for seed in 0..300u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xfac7_2000 + seed),
            max_w: 6,
            vars: Vec::new(),
        };
        let w = 1 + g.rng.below(6) as u16;
        let (a, _) = g.expr(&mut cx, w, 4);
        let (b, _) = g.expr(&mut cx, w, 3);
        let ww = width(w);
        let c1 = BitVec::wrapping_from_u64(ww, g.rng.next());
        let c2 = BitVec::wrapping_from_u64(ww, g.rng.next());
        let (lo, hi) = if range::ule(&c1, &c2) {
            (c1, c2)
        } else {
            (c2, c1)
        };
        let (slo, shi) = if sle(&c1, &c2) { (c1, c2) } else { (c2, c1) };
        let bit = g.rng.below(u64::from(w)) as u16;
        let bits = g.rng.below(u64::from(w) + 1) as u16;
        let queries: Vec<(Query<'_>, Holds)> = vec![
            (
                Query::IsZero(a),
                Box::new(|x: &BitVec, _: &BitVec| x.is_zero()),
            ),
            (
                Query::IsNonZero(a),
                Box::new(|x: &BitVec, _: &BitVec| !x.is_zero()),
            ),
            (
                Query::Bit {
                    e: a,
                    bit,
                    value: true,
                },
                Box::new(move |x: &BitVec, _: &BitVec| x.bit(bit) == Some(true)),
            ),
            (Query::Eq(a, b), Box::new(|x: &BitVec, y: &BitVec| x == y)),
            (
                Query::Cmp(CmpOpExt::Ult, a, b),
                Box::new(|x: &BitVec, y: &BitVec| BitVec::apply_cmp(CmpOpExt::Ult, x, y).unwrap()),
            ),
            (
                Query::Cmp(CmpOpExt::Sge, a, b),
                Box::new(|x: &BitVec, y: &BitVec| BitVec::apply_cmp(CmpOpExt::Sge, x, y).unwrap()),
            ),
            (
                Query::InURange {
                    e: a,
                    lo: &lo,
                    hi: &hi,
                },
                Box::new(move |x: &BitVec, _: &BitVec| range::ule(&lo, x) && range::ule(x, &hi)),
            ),
            (
                Query::InSRange {
                    e: a,
                    lo: &slo,
                    hi: &shi,
                },
                Box::new(move |x: &BitVec, _: &BitVec| sle(&slo, x) && sle(x, &shi)),
            ),
            (
                Query::Aligned { e: a, log2: bits },
                Box::new(move |x: &BitVec, _: &BitVec| known::trailing_zeros(x) >= u32::from(bits)),
            ),
            (
                Query::MaskRedundant { e: a, mask: &c1 },
                Box::new(move |x: &BitVec, _: &BitVec| known::bv_and(x, &c1) == *x),
            ),
            (
                Query::FitsUnsigned { e: a, bits },
                Box::new(move |x: &BitVec, _: &BitVec| {
                    known::leading_zeros(x) >= u32::from(w - bits.min(w))
                }),
            ),
            (
                Query::FitsSigned { e: a, bits },
                Box::new(move |x: &BitVec, _: &BitVec| {
                    if bits == 0 {
                        return false;
                    }
                    let s = x.to_i128().unwrap();
                    let half = 1i128 << (bits - 1);
                    -half <= s && s < half
                }),
            ),
        ];
        for (q, holds) in queries {
            let t = cx.prove(q).unwrap();
            if t == Truth::Unknown {
                continue;
            }
            proved += 1;
            for _ in 0..40 {
                let env = random_env(&mut g);
                let v = cx.eval(&[a, b], &env).unwrap();
                assert_eq!(
                    holds(&v[0], &v[1]),
                    t == Truth::True,
                    "{q:?} proved {t:?} but fails at {} / {}: a = {}, b = {}",
                    v[0],
                    v[1],
                    cx.display(a),
                    cx.display(b)
                );
            }
        }
    }
    assert!(
        proved > 300,
        "the proof suite should decide a good share of queries ({proved})"
    );
}

#[test]
fn work_cap_gives_top_then_progresses() {
    let mut cx = Context::with_config(crate::ContextConfig::default().with_fact_work(1000));
    let w = Width::W32;
    let x = cx.symbol("x", w).unwrap();
    let mask = cx.constant_u64(w, 0xff).unwrap();
    let mut e = cx.and(x, mask).unwrap();
    let one = cx.one(w).unwrap();
    for _ in 0..5000 {
        e = cx.lshr(e, one).unwrap();
    }
    // The chain is 5000 deep: the first query hits the cap.
    assert_eq!(cx.try_facts(e).unwrap(), None);
    assert_eq!(cx.facts(e).unwrap(), Facts::top(w));
    let mut rounds = 0;
    while cx.try_facts(e).unwrap().is_none() {
        rounds += 1;
        assert!(rounds < 10, "each query must make progress");
    }
    let f = cx.facts(e).unwrap();
    assert_eq!(f.as_constant(), Some(BitVec::zero(w)), "{f:?}");
}

#[test]
fn assumptions_refine_without_polluting_base_facts() {
    let mut cx = Context::new();
    let w = Width::W16;
    let x = cx.symbol("x", w).unwrap();
    let one = cx.one(w).unwrap();
    let e = cx.add(x, one).unwrap();
    let ten = BitVec::from_u64(w, 10).unwrap();
    let small = Facts::reduce(
        KnownBits::unknown(w),
        URange::new(BitVec::zero(w), ten).unwrap(),
        SRange::full(w),
    )
    .unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, x, small).unwrap();
    let f = cx.facts_with(e, &a).unwrap().unwrap();
    assert_eq!(f.urange.lo().to_u64(), Some(1));
    assert_eq!(f.urange.hi().to_u64(), Some(11));
    assert!(
        cx.facts(e).unwrap().urange.is_full(),
        "base facts unchanged"
    );
    let eleven = BitVec::from_u64(w, 11).unwrap();
    let q = Query::InURange {
        e,
        lo: &BitVec::one(w),
        hi: &eleven,
    };
    assert_eq!(cx.prove_with(q, &a).unwrap(), Truth::True);
    assert_eq!(cx.prove(q).unwrap(), Truth::Unknown);
    // A contradictory assumption is infeasible.
    let big = Facts::constant(&BitVec::from_u64(w, 500).unwrap());
    a.assume(&mut cx, x, big).unwrap();
    assert!(a.is_infeasible());
    assert_eq!(cx.facts_with(e, &a).unwrap(), None);
}

#[test]
fn precision_examples() {
    let mut cx = Context::new();
    let w = Width::W32;
    let x = cx.symbol("x", w).unwrap();
    let p = |cx: &mut Context, src: &str| cx.parse(src, &crate::ParseOptions::width(w)).unwrap();
    // Masks, shifts and extensions.
    let e = p(&mut cx, "x & 0xf0");
    assert_eq!(
        cx.prove(Query::Aligned { e, log2: 4 }).unwrap(),
        Truth::True
    );
    assert_eq!(
        cx.prove(Query::FitsUnsigned { e, bits: 8 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "x | 1");
    assert_eq!(cx.prove(Query::IsNonZero(e)).unwrap(), Truth::True);
    let e = p(&mut cx, "x * 8");
    assert_eq!(
        cx.prove(Query::Aligned { e, log2: 3 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "(x << 4) * (y << 2)");
    assert_eq!(
        cx.prove(Query::Aligned { e, log2: 6 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "zext<64>(trunc<8>(x))");
    assert_eq!(cx.facts(e).unwrap().urange.hi().to_u64(), Some(255));
    let e = p(&mut cx, "udiv(x, 16)");
    assert_eq!(
        cx.prove(Query::FitsUnsigned { e, bits: 28 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "urem(x, 10)");
    assert_eq!(cx.facts(e).unwrap().urange.hi().to_u64(), Some(9));
    let e = p(&mut cx, "clz(x | 0x10000)");
    let f = cx.facts(e).unwrap();
    assert_eq!(
        (f.urange.lo().to_u64(), f.urange.hi().to_u64()),
        (Some(0), Some(15))
    );
    let e = p(&mut cx, "pext(x, 0xff00)");
    assert_eq!(
        cx.prove(Query::FitsUnsigned { e, bits: 8 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "(x & 0xff) <u 256");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::from_bool(true)));
    let e = p(&mut cx, "sext<32>(trunc<8>(x)) <s 128");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::from_bool(true)));
    let e = p(&mut cx, "(x | 1) == 0");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::from_bool(false)));
    // Value sets.
    let e = p(&mut cx, "(x & 3) + 4");
    let mut vs: Vec<u64> = cx
        .enumerate_values(e, 8)
        .unwrap()
        .unwrap()
        .iter()
        .map(|v| v.to_u64().unwrap())
        .collect();
    vs.sort_unstable();
    assert_eq!(vs, vec![4, 5, 6, 7]);
    assert_eq!(cx.enumerate_values(x, 8).unwrap(), None);
}

// ----- precision: the transfers that should be optimal are optimal ----------------------------

/// The most precise known bits of `{op(args) | args in the inputs' concretizations}`.
fn best_known(op: &TOp, ins: &[&Facts]) -> Option<KnownBits> {
    let sets: Vec<Vec<BitVec>> = ins.iter().map(|f| members(f)).collect();
    if sets.iter().any(|s| s.is_empty()) {
        return None;
    }
    let mut best: Option<KnownBits> = None;
    let mut idx = vec![0usize; sets.len()];
    loop {
        let args: Vec<BitVec> = idx.iter().zip(&sets).map(|(&i, s)| s[i]).collect();
        let k = KnownBits::constant(&eval_top(op, &args));
        best = Some(best.map_or(k, |b| b.hull(&k)));
        let mut j = 0;
        loop {
            if j == idx.len() {
                return best;
            }
            idx[j] += 1;
            if idx[j] < sets[j].len() {
                break;
            }
            idx[j] = 0;
            j += 1;
        }
    }
}

#[test]
fn known_bits_transfers_are_optimal_where_expected() {
    let mut rng = Rng(0xfac7_0005);
    for w in 1..=3u16 {
        // Pure known-bits input states (ranges only as implied by the bits).
        let st: Vec<Facts> = states(&mut rng, w, 0);
        let check = |op: TOp, ins: &[&Facts]| {
            let Some(best) = best_known(&op, ins) else {
                return;
            };
            let got = transfer(&op, ins).known;
            assert_eq!(got, best, "{op:?} not optimal for {ins:?}");
        };
        for a in &st {
            for op in [UnOp::Not, UnOp::Neg, UnOp::BitRev] {
                check(TOp::Un(op), &[a]);
            }
            for to in (w + 1)..=(w + 2) {
                check(TOp::Zext(width(to)), &[a]);
                check(TOp::Sext(width(to)), &[a]);
            }
            for lo in 0..w {
                check(
                    TOp::Extract {
                        lo,
                        width: width(w - lo),
                    },
                    &[a],
                );
            }
            for b in &st {
                for op in [BinOp::And, BinOp::Or, BinOp::Xor, BinOp::Add, BinOp::Sub] {
                    check(TOp::Bin(op), &[a, b]);
                }
            }
            for c in 0..(u64::from(w) + 2) {
                let cf = Facts::constant(&BitVec::wrapping_from_u64(width(w), c));
                for op in [
                    BinOp::Shl,
                    BinOp::LShr,
                    BinOp::AShr,
                    BinOp::RotL,
                    BinOp::RotR,
                ] {
                    check(TOp::Bin(op), &[a, &cf]);
                }
            }
        }
    }
}

#[test]
fn range_transfers_keep_their_bounds() {
    let w = Width::W16;
    let r = |lo: u64, hi: u64| {
        Facts::reduce(
            KnownBits::unknown(w),
            URange::new(
                BitVec::wrapping_from_u64(w, lo),
                BitVec::wrapping_from_u64(w, hi),
            )
            .unwrap(),
            SRange::full(w),
        )
        .unwrap()
    };
    let hi = |f: Facts| f.urange.hi().to_u64().unwrap();
    let lo = |f: Facts| f.urange.lo().to_u64().unwrap();
    let (a, b) = (r(3, 9), r(20, 200));
    assert_eq!(hi(transfer(&TOp::Bin(BinOp::And), &[&a, &b])), 9);
    assert_eq!(lo(transfer(&TOp::Bin(BinOp::Or), &[&a, &b])), 20);
    let s = transfer(&TOp::Bin(BinOp::Add), &[&a, &b]);
    assert_eq!((lo(s), hi(s)), (23, 209));
    let d = transfer(&TOp::Bin(BinOp::Sub), &[&b, &a]);
    assert_eq!((lo(d), hi(d)), (11, 197));
    let m = transfer(&TOp::Bin(BinOp::Mul), &[&a, &b]);
    assert_eq!((lo(m), hi(m)), (60, 1800));
    let q = transfer(&TOp::Bin(BinOp::UDiv), &[&b, &a]);
    assert_eq!((lo(q), hi(q)), (2, 66));
    let rem = transfer(&TOp::Bin(BinOp::URem), &[&b, &a]);
    assert_eq!(hi(rem), 8);
}

// ----- regressions from the M2 review ---------------------------------------------------------

#[test]
fn mixed_widths_are_rejected_by_the_public_lattice_operations() {
    let (a, b) = (Facts::top(Width::W8), Facts::top(Width::W16));
    assert!(a.meet(&b).is_none());
    assert!(a.join(&b).is_none());
    assert!(a.known().meet(&b.known()).is_none());
    assert!(a.urange().join(&b.urange()).is_none());
    assert!(Facts::new(a.known(), b.urange(), a.srange()).is_none());
    assert!(Facts::new(a.known(), a.urange(), a.srange()).is_some());
}

#[test]
fn overlays_follow_the_exact_assumption_set() {
    let mut cx = Context::new();
    let w = Width::W64;
    let x = cx.symbol("x", w).unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, x, Facts::constant(&BitVec::zero(w)))
        .unwrap();
    let mut b = Assumptions::new();
    b.assume(&mut cx, x, Facts::from_known(KnownBits::unknown(w)))
        .unwrap();
    for _ in 0..3 {
        assert_eq!(cx.prove_with(Query::IsZero(x), &a).unwrap(), Truth::True);
        assert_eq!(cx.prove_with(Query::IsZero(x), &b).unwrap(), Truth::Unknown);
    }
}

#[test]
fn infeasible_assumptions_answer_true_after_validation() {
    let mut cx = Context::new();
    let w = Width::W8;
    let x = cx.symbol("x", w).unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, x, Facts::constant(&BitVec::zero(w)))
        .unwrap();
    a.assume(&mut cx, x, Facts::constant(&BitVec::one(w)))
        .unwrap();
    assert!(a.is_infeasible());
    assert_eq!(cx.prove_with(Query::IsNonZero(x), &a).unwrap(), Truth::True);
    assert_eq!(cx.prove_with(Query::IsZero(x), &a).unwrap(), Truth::True);
    assert!(
        cx.prove_with(
            Query::Bit {
                e: x,
                bit: 99,
                value: true
            },
            &a
        )
        .is_err()
    );
    assert!(
        cx.prove(Query::Bit {
            e: x,
            bit: 99,
            value: true
        })
        .is_err()
    );
}

#[test]
fn capped_queries_resume_linearly() {
    let mut cx = Context::with_config(crate::ContextConfig::default().with_fact_work(1000));
    let w = Width::W32;
    let x = cx.symbol("x", w).unwrap();
    let one = cx.one(w).unwrap();
    let mut e = x;
    for _ in 0..100_000 {
        e = cx.add(e, one).unwrap();
    }
    let mut calls = 0;
    while cx.try_facts(e).unwrap().is_none() {
        calls += 1;
    }
    assert!(
        calls <= 101,
        "each call should run a full cap of transfers ({calls} calls)"
    );
    // A zero cap still makes progress.
    let mut cx0 = Context::with_config(crate::ContextConfig::default().with_fact_work(0));
    let y = cx0.symbol("y", w).unwrap();
    let e0 = cx0.not(y).unwrap();
    let mut n = 0;
    while cx0.try_facts(e0).unwrap().is_none() {
        n += 1;
        assert!(n < 10);
    }
}

#[test]
fn assumptions_on_small_parts_of_large_cached_dags_stay_precise() {
    let mut cx = Context::with_config(crate::ContextConfig::default().with_fact_work(1000));
    let w = Width::W32;
    let x = cx.symbol("x", w).unwrap();
    let one = cx.one(w).unwrap();
    let mut e = x;
    for _ in 0..50_000 {
        e = cx.add(e, one).unwrap();
    }
    while cx.try_facts(e).unwrap().is_none() {}
    let z = cx.symbol("z", w).unwrap();
    let t = cx.and(e, z).unwrap();
    let mut a = Assumptions::new();
    a.assume(&mut cx, z, Facts::constant(&BitVec::zero(w)))
        .unwrap();
    assert_eq!(cx.prove_with(Query::IsZero(t), &a).unwrap(), Truth::True);
}

#[test]
fn enumeration_is_bounded_and_range_based() {
    assert!(KnownBits::unknown(Width::W64).enumerate(40).is_none());
    let mut cx = Context::new();
    let e = cx
        .parse("(x & 15) + 3", &crate::ParseOptions::width(Width::W32))
        .unwrap();
    let vs = cx.enumerate_values(e, 16).unwrap().unwrap();
    assert_eq!(vs.len(), 16);
    let e3 = cx
        .parse("(x & 3) + 1", &crate::ParseOptions::width(Width::W32))
        .unwrap();
    assert!(
        cx.enumerate_values(e3, 3).unwrap().is_none(),
        "four values exceed a limit of three"
    );
    assert_eq!(cx.enumerate_values(e3, 4).unwrap().unwrap().len(), 4);
    let c = cx
        .parse("(x & 0) + 7", &crate::ParseOptions::width(Width::W32))
        .unwrap();
    assert_eq!(cx.prove(Query::IsConstant(c)).unwrap(), Truth::True);
    assert_eq!(cx.prove(Query::IsConstant(e)).unwrap(), Truth::Unknown);
}

#[test]
fn precision_for_masked_counts_signed_products_and_divisions() {
    let mut cx = Context::new();
    let p = |cx: &mut Context, src: &str| cx.parse(src, &crate::ParseOptions::default()).unwrap();
    let e = p(&mut cx, "16:64 << (y:64 & 31)");
    assert_eq!(
        cx.prove(Query::FitsUnsigned { e, bits: 36 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "0xffff0000:32 >>u (y32:32 & 31)");
    assert_eq!(
        cx.facts(e).unwrap().urange().hi().to_u64(),
        Some(0xffff_0000)
    );
    let e = p(&mut cx, "sext<32>(a:8) * sext<32>(b:8)");
    assert_eq!(
        cx.prove(Query::FitsSigned { e, bits: 16 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "sdiv(sext<32>(a:8), zext<32>(c:4) + 1)");
    assert_eq!(
        cx.prove(Query::FitsSigned { e, bits: 8 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "srem(sext<32>(a:8), zext<32>(c:4) + 1)");
    assert_eq!(
        cx.prove(Query::FitsSigned { e, bits: 6 }).unwrap(),
        Truth::True
    );
    let e = p(&mut cx, "sext<32>(a:8) >>s (d:32 & 7)");
    assert_eq!(
        cx.prove(Query::FitsSigned { e, bits: 8 }).unwrap(),
        Truth::True
    );
}

// ----- backward transfer and constraints --------------------------------------------------------

/// Checks `backward(op, r, ins)` against every operand tuple inside `ins` whose result is in `r`.
fn check_backward(op: &TOp, r: &Facts, ins: &[&Facts]) {
    let out = super::backward::backward(op, r, ins);
    let sets: Vec<Vec<BitVec>> = ins.iter().map(|f| members(f)).collect();
    if sets.iter().any(|s| s.is_empty()) {
        return;
    }
    let mut idx = vec![0usize; sets.len()];
    loop {
        let args: Vec<BitVec> = idx.iter().zip(&sets).map(|(&i, s)| s[i]).collect();
        let v = eval_top(op, &args);
        if r.contains(&v) {
            let Some(out) = &out else {
                panic!("{op:?}: {r:?} called infeasible, but {args:?} -> {v} (inputs {ins:?})");
            };
            for (k, a) in args.iter().enumerate() {
                if let Some(f) = &out[k] {
                    assert!(
                        f.contains(a),
                        "{op:?} backward unsound: result {r:?}, inputs {ins:?}, values {args:?} \
                         -> {v}, operand {k} not in {f:?}"
                    );
                }
            }
        }
        let mut k = 0;
        loop {
            if k == idx.len() {
                return;
            }
            idx[k] += 1;
            if idx[k] < sets[k].len() {
                break;
            }
            idx[k] = 0;
            k += 1;
        }
    }
}

/// Result facts to assume at width `w`: every constant, and a sample of other states.
fn results(rng: &mut Rng, w: u16, random: usize) -> Vec<Facts> {
    let mut out: Vec<Facts> = all_values(w).iter().map(Facts::constant).collect();
    out.extend(states(rng, w, random));
    out
}

#[test]
fn every_backward_transfer_is_sound_exhaustively() {
    let mut rng = Rng(0xbac4_0001);
    for w in 1..=3u16 {
        let st = states(&mut rng, w, 12);
        let rs = results(&mut rng, w, 6);
        let ones = results(&mut rng, 1, 0);
        for r in &rs {
            for a in &st {
                for op in UnOp::ALL {
                    if op == UnOp::Bswap && !w.is_multiple_of(8) {
                        continue;
                    }
                    check_backward(&TOp::Un(op), r, &[a]);
                }
                for b in st.iter().take(20) {
                    for op in BinOp::ALL {
                        check_backward(&TOp::Bin(op), r, &[a, b]);
                    }
                }
            }
            for t in st.iter().take(10) {
                for e in st.iter().take(10) {
                    for c in &ones {
                        check_backward(&TOp::Select, r, &[c, t, e]);
                    }
                }
            }
        }
        // Comparisons: results are 1-bit.
        for r in &ones {
            for a in &st {
                for b in &st {
                    for op in CmpOp::ALL {
                        check_backward(&TOp::Cmp(op), r, &[a, b]);
                    }
                }
            }
        }
        // Casts, extraction and concatenation, with results of their own widths.
        for a in &st {
            for to in (w + 1)..=(w + 2) {
                for r in results(&mut rng, to, 4) {
                    check_backward(&TOp::Zext(width(to)), &r, &[a]);
                    check_backward(&TOp::Sext(width(to)), &r, &[a]);
                }
            }
            for lo in 0..w {
                for len in 1..=(w - lo) {
                    for r in results(&mut rng, len, 2) {
                        let op = TOp::Extract {
                            lo,
                            width: width(len),
                        };
                        check_backward(&op, &r, &[a]);
                    }
                }
            }
            for b in states(&mut rng, 2, 4) {
                for r in results(&mut rng, w + 2, 2).iter().step_by(3) {
                    check_backward(&TOp::Concat, r, &[a, &b]);
                }
            }
        }
    }
}

#[test]
fn backward_transfers_are_sound_on_sampled_states() {
    let mut rng = Rng(0xbac4_0002);
    // 8 bits too, for the byte swap (defined only at multiples of 8).
    for w in [4u16, 5, 6, 8] {
        let st = states(&mut rng, w, 30);
        let rs = results(&mut rng, w, 30);
        for _ in 0..1500 {
            let a = &st[rng.below(st.len() as u64) as usize];
            let b = &st[rng.below(st.len() as u64) as usize];
            let r = &rs[rng.below(rs.len() as u64) as usize];
            check_backward(&TOp::Bin(BinOp::ALL[rng.below(19) as usize]), r, &[a, b]);
            let u = UnOp::ALL[rng.below(7) as usize];
            if u != UnOp::Bswap || w.is_multiple_of(8) {
                check_backward(&TOp::Un(u), r, &[a]);
            }
            let one = Facts::constant(&BitVec::from_bool(rng.chance(1, 2)));
            check_backward(&TOp::Cmp(CmpOp::ALL[rng.below(6) as usize]), &one, &[a, b]);
        }
    }
}

/// Every assignment of the symbols of `vars` (at most 2^12 of them).
fn every_env(vars: &[(String, u16)]) -> Option<Vec<HashMap<SymbolKey, BitVec>>> {
    let bits: u32 = vars.iter().map(|(_, w)| u32::from(*w)).sum();
    if bits > 12 {
        return None;
    }
    Some(
        (0..(1u64 << bits))
            .map(|code| {
                let mut c = code;
                vars.iter()
                    .map(|(n, w)| {
                        let v = BitVec::wrapping_from_u64(width(*w), c);
                        c >>= w;
                        (SymbolKey::from(n.as_str()), v)
                    })
                    .collect()
            })
            .collect(),
    )
}

/// A random 1-bit predicate over subexpressions of a random expression.
fn random_predicate(g: &mut Gen, cx: &mut Context, depth: u32) -> Expr {
    let w = 1 + g.rng.below(3) as u16;
    let atom = |g: &mut Gen, cx: &mut Context| -> Expr {
        let (a, _) = g.expr(cx, w, depth);
        match g.rng.below(4) {
            0 => {
                // (a & m) == c
                let m = cx.constant(&g.constant(w)).unwrap();
                let c = cx.constant(&g.constant(w)).unwrap();
                let am = cx.bin(BinOp::And, a, m).unwrap();
                cx.cmp(CmpOp::Eq, am, c).unwrap()
            }
            1 => {
                let c = cx.constant(&g.constant(w)).unwrap();
                let op = CmpOpExt::ALL[g.rng.below(10) as usize];
                cx.cmp(op, a, c).unwrap()
            }
            _ => {
                let (b, _) = g.expr(cx, w, depth);
                let op = CmpOpExt::ALL[g.rng.below(10) as usize];
                cx.cmp(op, a, b).unwrap()
            }
        }
    };
    let p = atom(g, cx);
    match g.rng.below(4) {
        0 => {
            let q = atom(g, cx);
            cx.bin(BinOp::And, p, q).unwrap()
        }
        1 => {
            let q = atom(g, cx);
            cx.bin(BinOp::Or, p, q).unwrap()
        }
        2 => cx.un(UnOp::Not, p).unwrap(),
        _ => p,
    }
}

#[test]
fn constraints_are_sound_under_every_satisfying_assignment() {
    let mut checked = 0u32;
    let mut refined = 0u32;
    for seed in 0..400u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xc0de_0000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let n = 1 + g.rng.below(3);
        let preds: Vec<(Expr, bool)> = (0..n)
            .map(|_| (random_predicate(&mut g, &mut cx, 2), g.rng.chance(2, 3)))
            .collect();
        let w = 1 + g.rng.below(3) as u16;
        let (probe, _) = g.expr(&mut cx, w, 3);
        let Some(envs) = every_env(&g.vars) else {
            continue;
        };
        let mut a = Assumptions::new();
        for &(p, v) in &preds {
            if v {
                a.assume_true(&mut cx, p).unwrap();
            } else {
                a.assume_false(&mut cx, p).unwrap();
            }
        }
        let mut nodes: Vec<Expr> = preds.iter().map(|&(p, _)| p).collect();
        nodes.push(probe);
        let all = cx.post_order(&nodes).unwrap();
        let facts: Vec<Option<Facts>> =
            all.iter().map(|&x| cx.facts_with(x, &a).unwrap()).collect();
        let mut satisfiable = false;
        for env in &envs {
            let vals = cx.eval(&all, env).unwrap();
            let pv = cx
                .eval(&preds.iter().map(|&(p, _)| p).collect::<Vec<_>>(), env)
                .unwrap();
            if !preds
                .iter()
                .zip(&pv)
                .all(|(&(_, want), got)| got.is_zero() != want)
            {
                continue;
            }
            satisfiable = true;
            checked += 1;
            for ((x, f), v) in all.iter().zip(&facts).zip(&vals) {
                let f = f.unwrap_or_else(|| {
                    panic!("seed {seed}: satisfiable constraints called infeasible")
                });
                assert!(
                    f.contains(v),
                    "seed {seed}: {} = {v} under {:?}, not in {f:?}",
                    cx.display(*x),
                    a
                );
            }
        }
        if !satisfiable {
            continue;
        }
        assert!(
            !a.is_infeasible(),
            "seed {seed}: satisfiable, called infeasible"
        );
        for (x, f) in all.iter().zip(&facts) {
            if f.is_some_and(|f| f != cx.facts(*x).unwrap()) {
                refined += 1;
            }
        }
    }
    assert!(
        checked > 5_000,
        "only {checked} satisfying assignments checked"
    );
    assert!(refined > 500, "constraints refined only {refined} facts");
}

#[test]
fn infeasible_constraints_have_no_satisfying_assignment() {
    let mut infeasible = 0;
    for seed in 0..600u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xc0de_4000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let preds: Vec<(Expr, bool)> = (0..3)
            .map(|_| (random_predicate(&mut g, &mut cx, 1), g.rng.chance(1, 2)))
            .collect();
        let Some(envs) = every_env(&g.vars) else {
            continue;
        };
        let mut a = Assumptions::new();
        for &(p, v) in &preds {
            if v {
                a.assume_true(&mut cx, p).unwrap();
            } else {
                a.assume_false(&mut cx, p).unwrap();
            }
        }
        if !a.is_infeasible() {
            continue;
        }
        infeasible += 1;
        let conflict = a.conflict().unwrap();
        let ps: Vec<Expr> = preds.iter().map(|&(p, _)| p).collect();
        for env in &envs {
            let pv = cx.eval(&ps, env).unwrap();
            // The conflicting constraints alone are unsatisfiable.
            let all_hold = (0..3).all(|i| {
                !conflict.may_use(a.constraints().nth(i).unwrap().0)
                    || pv[i].is_zero() != preds[i].1
            });
            assert!(
                !all_hold,
                "seed {seed}: {env:?} satisfies the conflict {conflict:?}"
            );
        }
    }
    assert!(infeasible > 20, "only {infeasible} infeasible sets");
}

#[test]
fn proofs_under_constraints_are_sound_and_report_what_they_rely_on() {
    let mut proved = 0;
    for seed in 0..300u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xc0de_8000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let preds: Vec<Expr> = (0..2)
            .map(|_| random_predicate(&mut g, &mut cx, 1))
            .collect();
        let w = 1 + g.rng.below(3) as u16;
        let (x, _) = g.expr(&mut cx, w, 2);
        let (y, _) = g.expr(&mut cx, w, 2);
        let Some(envs) = every_env(&g.vars) else {
            continue;
        };
        let mut a = Assumptions::new();
        let ids: Vec<ConstraintId> = preds
            .iter()
            .map(|&p| a.assume_true(&mut cx, p).unwrap())
            .collect();
        if a.is_infeasible() {
            continue;
        }
        for op in CmpOpExt::ALL {
            let p = cx.prove_under(Query::Cmp(op, x, y), &a).unwrap();
            if p.truth == Truth::Unknown {
                assert!(p.relies_on.is_none());
                continue;
            }
            proved += 1;
            let want = p.truth == Truth::True;
            for env in &envs {
                let pv = cx.eval(&preds, env).unwrap();
                // Only the constraints the proof relies on need to hold.
                let relied_hold = ids
                    .iter()
                    .zip(&pv)
                    .all(|(&id, v)| !p.relies_on.may_use(id) || !v.is_zero());
                if !relied_hold {
                    continue;
                }
                let v = cx.eval(&[x, y], env).unwrap();
                let got = BitVec::apply_cmp(op, &v[0], &v[1]).unwrap();
                assert_eq!(
                    got,
                    want,
                    "seed {seed}: {} {} {} proved {want} relying on {:?}, but {env:?}",
                    cx.display(x),
                    op.symbol(),
                    cx.display(y),
                    p.relies_on
                );
            }
        }
    }
    assert!(proved > 300, "only {proved} proofs");
}

#[test]
fn orderings_between_two_expressions_are_sound() {
    let mut decided = 0;
    for seed in 0..500u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xc0de_c000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let w = 2 + g.rng.below(2) as u16;
        let (x, _) = g.expr(&mut cx, w, 1);
        let (y, _) = g.expr(&mut cx, w, 1);
        let Some(envs) = every_env(&g.vars) else {
            continue;
        };
        // One or two comparisons of the pair, in either orientation, assumed either way.
        let mut a = Assumptions::new();
        let mut assumed = Vec::new();
        for _ in 0..1 + g.rng.below(2) {
            let op = CmpOpExt::ALL[g.rng.below(10) as usize];
            let (l, r) = if g.rng.chance(1, 2) { (x, y) } else { (y, x) };
            let p = cx.cmp(op, l, r).unwrap();
            let v = g.rng.chance(1, 2);
            if v {
                a.assume_true(&mut cx, p).unwrap();
            } else {
                a.assume_false(&mut cx, p).unwrap();
            }
            assumed.push((op, l, r, v));
        }
        let holds = |cx: &mut Context, env: &HashMap<SymbolKey, BitVec>| {
            assumed.iter().all(|&(op, l, r, v)| {
                let lr = cx.eval(&[l, r], env).unwrap();
                BitVec::apply_cmp(op, &lr[0], &lr[1]).unwrap() == v
            })
        };
        for op in CmpOpExt::ALL {
            for (l, r) in [(x, y), (y, x)] {
                let t = cx.prove_with(Query::Cmp(op, l, r), &a).unwrap();
                // The comparison node itself, under the overlay.
                let node = cx.cmp(op, l, r).unwrap();
                let f = cx.facts_with(node, &a).unwrap();
                if a.is_infeasible() {
                    continue;
                }
                if t != Truth::Unknown {
                    decided += 1;
                }
                for env in &envs {
                    if !holds(&mut cx, env) {
                        continue;
                    }
                    let lr = cx.eval(&[l, r], env).unwrap();
                    let got = BitVec::apply_cmp(op, &lr[0], &lr[1]).unwrap();
                    if t != Truth::Unknown {
                        assert_eq!(got, t == Truth::True, "seed {seed}: {op:?} under {a:?}");
                    }
                    assert!(
                        f.unwrap().contains(&BitVec::from_bool(got)),
                        "seed {seed}: facts of {op:?} under {a:?}"
                    );
                }
            }
        }
    }
    assert!(decided > 2_000, "only {decided} comparisons decided");
}

#[test]
fn public_transfers_are_sound_and_width_checked() {
    let mut rng = Rng(0xfac7_7777);
    for w in 1..=3u16 {
        let st = states(&mut rng, w, 10);
        for a in &st {
            for op in UnOp::ALL {
                let r = Facts::apply_un(op, a);
                if op == UnOp::Bswap {
                    assert!(r.is_err());
                    continue;
                }
                let r = r.unwrap();
                for x in members(a) {
                    assert!(r.contains(&BitVec::apply_un(op, &x).unwrap()));
                }
            }
            let k = KnownBits::apply_un(UnOp::Not, &a.known()).unwrap();
            for x in members(a) {
                assert!(k.contains(&BitVec::apply_un(UnOp::Not, &x).unwrap()));
            }
            for b in st.iter().take(6) {
                for op in BinOp::ALL {
                    let r = Facts::apply_bin(op, a, b).unwrap();
                    let kb = KnownBits::apply_bin(op, &a.known(), &b.known()).unwrap();
                    for x in members(a) {
                        for y in members(b) {
                            let v = BitVec::apply_bin(op, &x, &y).unwrap();
                            assert!(r.contains(&v) && kb.contains(&v), "{op:?}");
                        }
                    }
                }
                for op in CmpOpExt::ALL {
                    let r = Facts::apply_cmp(op, a, b).unwrap();
                    for x in members(a) {
                        for y in members(b) {
                            let v = BitVec::from_bool(BitVec::apply_cmp(op, &x, &y).unwrap());
                            assert!(r.contains(&v), "{op:?}");
                        }
                    }
                }
            }
            let z = a.zext(width(w + 2)).unwrap();
            let s = a.sext(width(w + 2)).unwrap();
            for x in members(a) {
                assert!(z.contains(&x.zext(width(w + 2)).unwrap()));
                assert!(s.contains(&x.sext(width(w + 2)).unwrap()));
            }
            assert_eq!(a.zext(a.width()).unwrap(), *a);
        }
    }
    let f8 = Facts::top(Width::W8);
    let f4 = Facts::top(width(4));
    assert!(Facts::apply_bin(BinOp::Add, &f8, &f4).is_err());
    assert!(Facts::apply_cmp(CmpOp::Eq, &f8, &f4).is_err());
    assert!(f8.zext(width(4)).is_err());
    assert!(f8.extract(6, width(4)).is_err());
    assert!(Facts::select(&f4, &f8, &f8).is_err());
    assert_eq!(Facts::concat(&f8, &f4).unwrap().width(), width(12));
    assert_eq!(f8.extract(4, width(4)).unwrap().width(), width(4));
}

#[test]
fn equalities_are_transitive() {
    let mut cx = Context::new();
    let o = crate::ParseOptions::width(Width::W32);
    let mut a = Assumptions::new();
    let p: Vec<Expr> = ["x == y", "y == z", "z <u w"]
        .iter()
        .map(|s| cx.parse(s, &o).unwrap())
        .collect();
    let ids: Vec<ConstraintId> = p
        .iter()
        .map(|&q| a.assume_true(&mut cx, q).unwrap())
        .collect();
    let (x, z, w) = (
        cx.parse("x", &o).unwrap(),
        cx.parse("z", &o).unwrap(),
        cx.parse("w", &o).unwrap(),
    );
    // x == z through y, and x <u w through z.
    let eq = cx.prove_under(Query::Eq(x, z), &a).unwrap();
    assert_eq!(eq.truth, Truth::True);
    assert!(eq.relies_on.may_use(ids[0]) && eq.relies_on.may_use(ids[1]));
    assert!(!eq.relies_on.may_use(ids[2]));
    let lt = cx.prove_under(Query::Cmp(CmpOpExt::Ult, x, w), &a).unwrap();
    assert_eq!(lt.truth, Truth::True);
    // The comparison node itself folds under the overlay.
    let node = cx.parse("x <=u w", &o).unwrap();
    assert_eq!(
        cx.facts_with(node, &a).unwrap().unwrap().as_constant(),
        Some(BitVec::one(Width::W1))
    );
    // And x != z contradicts the chain.
    let mut b = a.clone();
    let ne = cx.parse("x != z", &o).unwrap();
    let last = b.assume_true(&mut cx, ne).unwrap();
    let c = b.conflict().expect("x == y == z contradicts x != z");
    assert!(c.may_use(ids[0]) && c.may_use(ids[1]) && c.may_use(last) && !c.may_use(ids[2]));
    // Two orderings that leave only equality merge the classes.
    let mut e = Assumptions::new();
    for s in ["p <=u q", "q <=u p", "q <s r"] {
        let q = cx.parse(s, &o).unwrap();
        e.assume_true(&mut cx, q).unwrap();
    }
    let (p_, r_) = (cx.parse("p", &o).unwrap(), cx.parse("r", &o).unwrap());
    assert_eq!(
        cx.prove_with(Query::Cmp(CmpOpExt::Slt, p_, r_), &e)
            .unwrap(),
        Truth::True
    );
}

#[test]
fn orderings_among_three_expressions_are_sound() {
    let mut decided = 0;
    let mut infeasible = 0;
    for seed in 0..500u64 {
        let mut cx = Context::new();
        let mut g = Gen {
            rng: Rng(0xc0de_e000 + seed),
            max_w: 3,
            vars: Vec::new(),
        };
        let w = 2 + g.rng.below(2) as u16;
        let xs: Vec<Expr> = (0..3).map(|_| g.expr(&mut cx, w, 1).0).collect();
        let Some(envs) = every_env(&g.vars) else {
            continue;
        };
        let mut a = Assumptions::new();
        let mut assumed = Vec::new();
        for _ in 0..2 + g.rng.below(3) {
            let (i, j) = (g.rng.below(3) as usize, g.rng.below(3) as usize);
            if xs[i] == xs[j] {
                continue;
            }
            let op = CmpOpExt::ALL[g.rng.below(10) as usize];
            let p = cx.cmp(op, xs[i], xs[j]).unwrap();
            let v = g.rng.chance(2, 3);
            if v {
                a.assume_true(&mut cx, p).unwrap();
            } else {
                a.assume_false(&mut cx, p).unwrap();
            }
            assumed.push((op, xs[i], xs[j], v));
        }
        let sat: Vec<&HashMap<SymbolKey, BitVec>> = envs
            .iter()
            .filter(|env| {
                assumed.iter().all(|&(op, l, r, v)| {
                    let lr = cx.eval(&[l, r], *env).unwrap();
                    BitVec::apply_cmp(op, &lr[0], &lr[1]).unwrap() == v
                })
            })
            .collect();
        if a.is_infeasible() {
            infeasible += 1;
            assert!(
                sat.is_empty(),
                "seed {seed}: satisfiable, called infeasible"
            );
            continue;
        }
        for i in 0..3 {
            for j in 0..3 {
                if xs[i] == xs[j] {
                    continue;
                }
                for op in CmpOpExt::ALL {
                    let t = cx.prove_with(Query::Cmp(op, xs[i], xs[j]), &a).unwrap();
                    if t == Truth::Unknown {
                        continue;
                    }
                    decided += 1;
                    for env in &sat {
                        let lr = cx.eval(&[xs[i], xs[j]], *env).unwrap();
                        let got = BitVec::apply_cmp(op, &lr[0], &lr[1]).unwrap();
                        assert_eq!(got, t == Truth::True, "seed {seed}: {op:?} {i} {j}");
                    }
                }
            }
        }
    }
    assert!(
        decided > 3_000 && infeasible > 30,
        "decided {decided}, infeasible {infeasible}"
    );
}

#[test]
fn minimum_and_maximum_selects_bound_both_sides() {
    // Operands with varied facts at 4 bits: every min/max form, every assignment.
    let o = crate::ParseOptions::width(width(4));
    let shapes = [
        "x & 3",
        "x | 8",
        "(x & 5) + 2",
        "x",
        "y & 12",
        "y >>u 2",
        "-y",
    ];
    let mut cx = Context::new();
    let (x, y) = (cx.parse("x", &o).unwrap(), cx.parse("y", &o).unwrap());
    let _ = (x, y);
    for sa in shapes {
        for sb in shapes {
            let a = cx.parse(sa, &o).unwrap();
            let b = cx.parse(sb, &o).unwrap();
            let forms = [
                cx.umin(a, b).unwrap(),
                cx.umax(a, b).unwrap(),
                cx.smin(a, b).unwrap(),
                cx.smax(a, b).unwrap(),
            ];
            for e in forms {
                let f = cx.facts(e).unwrap();
                for vx in 0..16u64 {
                    for vy in 0..16u64 {
                        let env: HashMap<SymbolKey, BitVec> = [
                            (
                                SymbolKey::from("x"),
                                BitVec::wrapping_from_u64(width(4), vx),
                            ),
                            (
                                SymbolKey::from("y"),
                                BitVec::wrapping_from_u64(width(4), vy),
                            ),
                        ]
                        .into_iter()
                        .collect();
                        let v = cx.eval(&[e], &env).unwrap()[0];
                        assert!(f.contains(&v), "{}: {v} not in {f:?}", cx.display(e));
                    }
                }
            }
        }
    }
    // The bound the join of the arms misses.
    let a = cx.parse("x & 3", &o).unwrap();
    let m = cx.umin(a, y).unwrap();
    assert_eq!(cx.facts(m).unwrap().urange().hi().to_u64(), Some(3));
    let b = cx.parse("x | 8", &o).unwrap();
    let m = cx.umax(b, y).unwrap();
    assert_eq!(cx.facts(m).unwrap().urange().lo().to_u64(), Some(8));
    let s = cx.parse("y >>s 2", &o).unwrap();
    let m = cx.smax(s, x).unwrap();
    assert_eq!(cx.facts(m).unwrap().srange().lo().to_i128(), Some(-2));
}

#[test]
fn widening_products_bound_their_range() {
    let o = crate::ParseOptions::width(width(4));
    let mut cx = Context::new();
    let a = cx.parse("x | 2", &o).unwrap();
    let b = cx.parse("(y & 3) + 4", &o).unwrap();
    let wu = cx.mul_wide_u(a, b).unwrap();
    let ws = cx.mul_wide_s(a, b).unwrap();
    for (e, name) in [(wu, "u"), (ws, "s")] {
        let f = cx.facts(e).unwrap();
        for vx in 0..16u64 {
            for vy in 0..16u64 {
                let env: HashMap<SymbolKey, BitVec> = [
                    (
                        SymbolKey::from("x"),
                        BitVec::wrapping_from_u64(width(4), vx),
                    ),
                    (
                        SymbolKey::from("y"),
                        BitVec::wrapping_from_u64(width(4), vy),
                    ),
                ]
                .into_iter()
                .collect();
                let v = cx.eval(&[e], &env).unwrap()[0];
                assert!(f.contains(&v), "{name}: {v} not in {f:?}");
            }
        }
    }
    // The product of [2, 15] and [4, 7] is at least 8 (the halves alone say 0).
    assert_eq!(cx.facts(wu).unwrap().urange().lo().to_u64(), Some(8));
}
