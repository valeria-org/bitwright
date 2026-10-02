//! Fact soundness: every transfer, the reduced product, context-level facts and proofs.

use std::collections::HashMap;

use super::transfer::{TOp, transfer};
use super::*;
use crate::testutil::{Gen, Rng, width};
use crate::{BinOp, CmpOpExt, SymbolKey, UnOp};

#[test]
fn original_constraint_predicates_match_facts_membership_exhaustively() {
    let mut rng = Rng(0x824a_139e_552c_0697);
    for bits in 1..=8 {
        let w = width(bits);
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        let offset = cx.constant_u64(w, u64::from(bits % 3)).unwrap();
        let shifted = cx.add(x, offset).unwrap();
        for facts in states(&mut rng, bits, 32) {
            for subject in [x, shifted] {
                let mut assumptions = Assumptions::new();
                assumptions.assume(&mut cx, subject, facts).unwrap();
                let predicates = assumptions.predicates(&mut cx).unwrap();
                assert_eq!(predicates.len(), 1);
                for value in all_values(bits) {
                    let env = [(SymbolKey::from("x"), value)];
                    let evaluated = cx.eval(&[subject, predicates[0]], &env[..]).unwrap();
                    assert_eq!(
                        !evaluated[1].is_zero(),
                        facts.contains(&evaluated[0]),
                        "width={bits}, facts={facts:?}, value={value:?}"
                    );
                }
            }
        }
        assert!(cx.declared_known(x).unwrap().is_none());
    }
}

#[test]
fn wide_constraint_predicates_keep_signed_crossings_masks_and_nonzero_stride_origins() {
    let mut rng = Rng(0x364e_71ac_954b_2801);
    for bits in [32, 64, 65, 129, 512] {
        let w = width(bits);
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        let masks = KnownBits::new(
            BitVec::wrapping_from_u64(w, 0x8420),
            BitVec::wrapping_from_u64(w, 0x0041),
        )
        .unwrap();
        let lo = BitVec::wrapping_from_u64(w, 13);
        let hi = BitVec::wrapping_from_u64(w, 433);
        let stride = Facts::new(
            KnownBits::unknown(w),
            URange::strided(lo, hi, 7).unwrap(),
            SRange::full(w),
        )
        .unwrap();
        let crossing = Facts::new(
            KnownBits::unknown(w),
            URange::full(w),
            SRange::new(
                BitVec::wrapping_from_i128(w, -20),
                BitVec::wrapping_from_i128(w, 20),
            )
            .unwrap(),
        )
        .unwrap();
        for facts in [Facts::from_known(masks), stride, crossing, Facts::top(w)] {
            let mut assumptions = Assumptions::new();
            assumptions.assume(&mut cx, x, facts).unwrap();
            let predicate = assumptions.predicates(&mut cx).unwrap()[0];
            let mut values = (-21..=21)
                .map(|v| BitVec::wrapping_from_i128(w, v))
                .collect::<Vec<_>>();
            values.extend([lo, hi, BitVec::ones(w), BitVec::smin(w), BitVec::smax(w)]);
            for _ in 0..64 {
                let limbs = (0..8).map(|_| rng.next()).collect::<Vec<_>>();
                values.push(BitVec::wrapping_from_limbs(w, &limbs));
            }
            for value in values {
                let env = [(SymbolKey::from("x"), value)];
                let actual = cx.eval(&[predicate], &env[..]).unwrap()[0];
                assert_eq!(
                    !actual.is_zero(),
                    facts.contains(&value),
                    "width={bits}, facts={facts:?}, value={value:?}"
                );
            }
        }
    }
}

#[test]
fn constraint_predicates_preserve_original_seeds_and_handle_scope_checks() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    let mut assumptions = Assumptions::new();
    let one = BitVec::from_u64(Width::W8, 1).unwrap();
    let two = BitVec::from_u64(Width::W8, 2).unwrap();
    assumptions
        .assume(&mut cx, x, Facts::constant(&one))
        .unwrap();
    assumptions
        .assume(&mut cx, x, Facts::constant(&two))
        .unwrap();
    assert!(assumptions.is_infeasible());
    let predicates = assumptions.predicates(&mut cx).unwrap();
    assert_eq!(predicates.len(), 2);
    for value in all_values(8) {
        let env = [(SymbolKey::from("x"), value)];
        assert!(
            !cx.eval(&predicates, &env[..])
                .unwrap()
                .iter()
                .all(|v| !v.is_zero())
        );
    }
    let mut other = Context::new();
    assert!(matches!(
        assumptions.predicates(&mut other),
        Err(Error::ForeignExpr)
    ));
    cx.clear();
    assert!(matches!(
        assumptions.predicates(&mut cx),
        Err(Error::StaleExpr)
    ));
    assert!(
        Assumptions::new()
            .predicates(&mut other)
            .unwrap()
            .is_empty()
    );
}

#[test]
fn declaration_changes_refresh_constraint_propagation_and_preserve_seed_ids() {
    let mut cx = Context::new();
    let x = cx.symbol("x", Width::W8).unwrap();
    cx.declare_known(x, KnownBits::constant(&BitVec::zero(Width::W8)))
        .unwrap();
    let bounded = Facts::new(
        KnownBits::unknown(Width::W8),
        URange::new(
            BitVec::zero(Width::W8),
            BitVec::from_u64(Width::W8, 3).unwrap(),
        )
        .unwrap(),
        SRange::full(Width::W8),
    )
    .unwrap();
    let mut assumptions = Assumptions::new();
    let id = assumptions.assume(&mut cx, x, bounded).unwrap();
    cx.declare_known(x, KnownBits::unknown(Width::W8)).unwrap();
    let current = cx.facts_under(x, &assumptions).unwrap().unwrap().0;
    assert_eq!(current.urange().hi().to_u64(), Some(3));
    assert!(current.as_constant().is_none());
    assumptions.refresh(&mut cx).unwrap();
    assert_eq!(assumptions.constraint(id), Some((x, bounded)));
    let next = assumptions.assume(&mut cx, x, bounded).unwrap();
    assert_eq!(next.index(), id.index() + 1);

    cx.declare_known(
        x,
        KnownBits::constant(&BitVec::from_u64(Width::W8, 4).unwrap()),
    )
    .unwrap();
    assert!(cx.facts_under(x, &assumptions).unwrap().is_none());
    assumptions.refresh(&mut cx).unwrap();
    assert!(assumptions.is_infeasible());
    cx.declare_known(x, KnownBits::unknown(Width::W8)).unwrap();
    assert!(cx.facts_under(x, &assumptions).unwrap().is_some());
    assumptions.refresh(&mut cx).unwrap();
    assert!(!assumptions.is_infeasible());
    assert_eq!(assumptions.constraints().count(), 2);
}

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
/// random unsigned (strided) and signed intervals.
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
        match rng.below(4) {
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
            2 => {
                let u = random_strided(rng, w);
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

/// A random strided interval of `w` bits.
fn random_strided(rng: &mut Rng, w: u16) -> URange {
    let n = 1u64 << w;
    let lo = rng.below(n);
    let stride = 1 + rng.below(n - lo);
    let hi = lo + stride * rng.below((n - 1 - lo) / stride + 1);
    let v = |x: u64| BitVec::wrapping_from_u64(width(w), x);
    URange::strided(v(lo), v(hi), stride).unwrap()
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
        TOp::Fp(d) => crate::fp::eval(&d, args),
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
            let u = random_strided(&mut rng, w);
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

/// Every strided interval of `w` bits.
fn all_strided(w: u16) -> Vec<URange> {
    let n = 1u64 << w;
    let v = |x: u64| BitVec::wrapping_from_u64(width(w), x);
    let mut out = Vec::new();
    for lo in 0..n {
        out.push(URange::constant(&v(lo)));
        for hi in lo + 1..n {
            for s in (1..=hi - lo).filter(|s| (hi - lo) % s == 0) {
                out.push(URange::strided(v(lo), v(hi), s).unwrap());
            }
        }
    }
    out
}

fn set_of(u: &URange) -> Vec<u64> {
    let w = u.width().bits();
    (0..1u64 << w)
        .filter(|&x| u.contains(&BitVec::wrapping_from_u64(width(w), x)))
        .collect()
}

#[test]
fn narrow_reduction_matches_the_wide_one() {
    let mut rng = Rng(0xfac7_0006);
    for &w in &[
        1u16, 2, 3, 5, 8, 13, 16, 31, 32, 33, 63, 64, 65, 96, 127, 128,
    ] {
        let ww = width(w);
        let val = |rng: &mut Rng| {
            let limbs = match rng.below(4) {
                0 => [rng.below(16), 0],
                1 => [!rng.below(16), !0],
                _ => [rng.next(), rng.next()],
            };
            BitVec::wrapping_from_limbs(ww, &limbs)
        };
        for _ in 0..3000 {
            // Known bits: a few random positions known.
            let (mut z, mut o) = (0u128, 0u128);
            for _ in 0..rng.below(u64::from(w) + 1) {
                let b = 1u128 << rng.below(u64::from(w));
                if rng.chance(1, 2) {
                    z |= b;
                } else {
                    o |= b;
                }
            }
            let o = o & !z;
            let k = KnownBits::new(
                BitVec::wrapping_from_u128(ww, z),
                BitVec::wrapping_from_u128(ww, o),
            )
            .unwrap();
            let (a, b) = (val(&mut rng), val(&mut rng));
            let (lo, hi) = if ule(&a, &b) { (a, b) } else { (b, a) };
            let span = BitVec::bin_unchecked(BinOp::Sub, &hi, &lo);
            let stride = match rng.below(3) {
                0 => 1,
                _ => {
                    let s = 1 + rng.below(12);
                    if range::rem(&span, s) == 0 { s } else { 1 }
                }
            };
            let u = URange::strided(lo, hi, stride).unwrap();
            let (c, d) = (val(&mut rng), val(&mut rng));
            let s = if sle(&c, &d) {
                SRange::new(c, d)
            } else {
                SRange::new(d, c)
            }
            .unwrap();
            assert_eq!(
                Facts::reduce(k, u, s),
                Facts::reduce_wide(k, u, s),
                "{k:?} {u:?} {s:?}"
            );
        }
    }
}

#[test]
fn strided_intervals_are_their_sets() {
    let mut rng = Rng(0xfac7_0005);
    for w in 1..=4u16 {
        let all = all_strided(w);
        for a in &all {
            // The members are lo, lo + stride, ..., hi.
            let (lo, hi, s) = (
                a.lo().to_u64().unwrap(),
                a.hi().to_u64().unwrap(),
                a.stride(),
            );
            let want: Vec<u64> = if s == 0 {
                vec![lo]
            } else {
                (lo..=hi).step_by(s as usize).collect()
            };
            let ma = set_of(a);
            assert_eq!(ma, want, "{a:?}");
            // Residue classes: exactly the members in the class.
            for m in 1..=(1u64 << w) {
                let r = rng.below(m);
                let got = a.meet_class(r, m).map(|u| set_of(&u)).unwrap_or_default();
                let want: Vec<u64> = ma.iter().copied().filter(|x| x % m == r).collect();
                assert_eq!(got, want, "{a:?} class {r} mod {m}");
            }
            for _ in 0..if w <= 3 { all.len() } else { 60 } {
                let b = &all[rng.below(all.len() as u64) as usize];
                let mb = set_of(b);
                // The meet is exactly the intersection (the moduli are small).
                let common: Vec<u64> = ma.iter().copied().filter(|x| mb.contains(x)).collect();
                let got = a.meet(b).map(|u| set_of(&u)).unwrap_or_default();
                assert_eq!(got, common, "{a:?} meet {b:?}");
                // The hull contains both, and `within` is inclusion.
                let hull = set_of(&a.hull(b));
                assert!(
                    ma.iter().chain(&mb).all(|x| hull.contains(x)),
                    "{a:?} hull {b:?}"
                );
                assert_eq!(
                    a.within(b),
                    ma.iter().all(|x| mb.contains(x)),
                    "{a:?} within {b:?}"
                );
            }
        }
    }
}

#[test]
fn known_bits_find_their_nearest_members() {
    for w in 1..=5u16 {
        let vals = all_values(w);
        for code in 0..3u64.pow(u32::from(w)) {
            let (mut z, mut o, mut c) = (0u64, 0u64, code);
            for b in 0..w {
                match c % 3 {
                    0 => z |= 1 << b,
                    1 => o |= 1 << b,
                    _ => {}
                }
                c /= 3;
            }
            let v = |x: u64| BitVec::wrapping_from_u64(width(w), x);
            let k = KnownBits::new(v(z), v(o)).unwrap();
            for x in &vals {
                let next = vals.iter().find(|y| ule(x, y) && k.contains(y)).copied();
                let prev = vals
                    .iter()
                    .rev()
                    .find(|y| ule(y, x) && k.contains(y))
                    .copied();
                assert_eq!(k.next_member(x), next, "{k:?} next from {x}");
                assert_eq!(k.prev_member(x), prev, "{k:?} prev from {x}");
            }
        }
    }
}

#[test]
fn strides_and_known_bits_tighten_each_other() {
    let w = Width::W8;
    let v = |x: u64| BitVec::wrapping_from_u64(w, x);
    let u = |f: &Facts| {
        (
            f.urange.lo().to_u64().unwrap(),
            f.urange.hi().to_u64().unwrap(),
            f.urange.stride(),
        )
    };
    let odd = KnownBits::new(v(0), v(1)).unwrap();
    // Known bits move the ends to values they allow: the odd values in [4, 10] are 5, 7, 9.
    let f = Facts::new(odd, URange::new(v(4), v(10)).unwrap(), SRange::full(w)).unwrap();
    assert_eq!(u(&f), (5, 9, 2));
    // Signed ends too: the odd values in [-4, 4] are -3 to 3.
    let f = Facts::new(odd, URange::full(w), SRange::new(v(0xfc), v(4)).unwrap()).unwrap();
    assert_eq!((f.srange.lo(), f.srange.hi()), (v(0xfd), v(3)));
    // A stride's factor of two is known low bits: 3, 7, 11, 15 end in 11.
    let f = Facts::new(
        KnownBits::unknown(w),
        URange::strided(v(3), v(15), 4).unwrap(),
        SRange::full(w),
    )
    .unwrap();
    assert_eq!(
        (f.known.bit(0), f.known.bit(1), f.known.bit(2)),
        (Some(true), Some(true), None)
    );
    // Known low bits and a stride combine: 1 mod 4 and 0 mod 3 is 9 mod 12.
    let low01 = KnownBits::new(v(2), v(1)).unwrap();
    let f = Facts::new(
        low01,
        URange::strided(v(0), v(99), 3).unwrap(),
        SRange::full(w),
    )
    .unwrap();
    assert_eq!(u(&f), (9, 93, 12));
    // No odd value is a multiple of 2.
    assert!(
        Facts::new(
            odd,
            URange::strided(v(0), v(8), 2).unwrap(),
            SRange::full(w)
        )
        .is_none()
    );
    // One value is every bit.
    let f = Facts::new(
        KnownBits::unknown(w),
        URange::strided(v(6), v(12), 6).unwrap(),
        SRange::new(v(10), v(20)).unwrap(),
    )
    .unwrap();
    assert_eq!(f.as_constant(), Some(v(12)));

    // Through expressions: strides decide what bounds cannot.
    let mut cx = Context::new();
    let w = Width::W32;
    let p = |cx: &mut Context, src: &str| cx.parse(src, &crate::ParseOptions::width(w)).unwrap();
    let e = p(&mut cx, "(x & 7) * 3");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 21, 3));
    // Cached facts keep their stride.
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 21, 3));
    let e = p(&mut cx, "(x & 3) * 3 + 1 == 5");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::from_bool(false)));
    let e = p(&mut cx, "udiv((x & 7) * 6, 3)");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 14, 2));
    let e = p(&mut cx, "urem((x & 7) * 6 + 1, 3)");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::one(w)));
    let e = p(&mut cx, "select(x <u 5, 3, 9) == 5");
    assert_eq!(cx.exact(e).unwrap(), Some(BitVec::from_bool(false)));
    let e = p(&mut cx, "zext<64>((x & 3) * 5)");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 15, 5));
    let e = p(&mut cx, "concat(trunc<4>(x) & 2, trunc<4>(y) & 4)");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 36, 4));
    let e = p(&mut cx, "((x & 7) * 3) << 2");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 84, 12));
    let e = p(&mut cx, "((x & 7) * 12) >>u 2");
    assert_eq!(u(&cx.facts(e).unwrap()), (0, 21, 3));
    let e = p(&mut cx, "~((x & 7) * 3)");
    assert_eq!(cx.facts(e).unwrap().urange.stride(), 3);
    let e = p(&mut cx, "(x & 3) * 5 + 2");
    let mut vs: Vec<u64> = cx
        .enumerate_values(e, 8)
        .unwrap()
        .unwrap()
        .iter()
        .map(|v| v.to_u64().unwrap())
        .collect();
    vs.sort_unstable();
    assert_eq!(vs, vec![2, 7, 12, 17]);
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
fn bitwise_identities_preserve_ranges_strides_and_both_operand_reliances() {
    for bits in [8, 32, 64, 65, 129, 512] {
        let w = width(bits);
        for op in [BinOp::And, BinOp::Or, BinOp::Xor] {
            for swapped in [false, true] {
                let mut cx = Context::new();
                let x = cx.symbol("x", w).unwrap();
                let mask = cx.symbol("mask", w).unwrap();
                let result = if swapped {
                    cx.bin(op, mask, x).unwrap()
                } else {
                    cx.bin(op, x, mask).unwrap()
                };
                let (lo, hi, stride, mask_facts) = match op {
                    BinOp::And => {
                        let ones = BitVec::wrapping_from_u64(w, 15);
                        let known = KnownBits::new(BitVec::zero(w), ones).unwrap();
                        (4, 12, 4, Facts::from_known(known))
                    }
                    BinOp::Or => {
                        let ones = BitVec::wrapping_from_u64(w, 0xf0);
                        let zeros = known::bv_not(&ones);
                        let known = KnownBits::new(zeros, BitVec::zero(w)).unwrap();
                        (0xf0, 0xf5, 1, Facts::from_known(known))
                    }
                    _ => (4, 12, 4, Facts::constant(&BitVec::zero(w))),
                };
                let original = Facts::reduce(
                    KnownBits::unknown(w),
                    URange::strided(
                        BitVec::wrapping_from_u64(w, lo),
                        BitVec::wrapping_from_u64(w, hi),
                        stride,
                    )
                    .unwrap(),
                    SRange::full(w),
                )
                .unwrap();
                let base = cx.facts(result).unwrap();
                let mut assumptions = Assumptions::new();
                let input_id = assumptions.assume(&mut cx, x, original).unwrap();
                let mask_id = assumptions.assume(&mut cx, mask, mask_facts).unwrap();
                let (facts, reliance) = cx.facts_under(result, &assumptions).unwrap().unwrap();
                assert_eq!(facts, original);
                assert!(reliance.may_use(input_id));
                assert!(reliance.may_use(mask_id));
                assert_eq!(cx.facts(result).unwrap(), base);

                // Omitting either operand's requirement removes the identity or
                // its selected range, so the cached conditional result must go.
                for keep_mask in [false, true] {
                    let mut partial = Assumptions::new();
                    if keep_mask {
                        partial.assume(&mut cx, mask, mask_facts).unwrap();
                    } else {
                        partial.assume(&mut cx, x, original).unwrap();
                    }
                    assert_ne!(cx.facts_with(result, &partial).unwrap().unwrap(), original);
                }

                // A changing bit operation must keep its normal conservative
                // transfer. Supply an explicit value violating the identity.
                let (changed_mask, input) = match op {
                    BinOp::And => (7, 8),
                    BinOp::Or => (0x100, 0xf0),
                    _ => (1, 4),
                };
                if bits == 8 && op == BinOp::Or {
                    continue;
                }
                let changed = cx.constant_u64(w, changed_mask).unwrap();
                let changed = cx.bin(op, x, changed).unwrap();
                let mut input_only = Assumptions::new();
                input_only.assume(&mut cx, x, original).unwrap();
                let output_facts = cx.facts_with(changed, &input_only).unwrap().unwrap();
                let model = [(SymbolKey::from("x"), BitVec::wrapping_from_u64(w, input))];
                let value = cx.eval(&[changed], &model[..]).unwrap()[0];
                assert!(output_facts.contains(&value));
                assert_ne!(value, BitVec::wrapping_from_u64(w, input));
                assert_ne!(output_facts, original);
            }
        }
    }
}

#[test]
fn redundant_selector_masks_preserve_the_conditional_shift_lower_bound() {
    for text in [
        "(h >>u 32) >>u ((h >>u 60) & 63)",
        "h >>u (32 + ((h >>u 60) & 63))",
    ] {
        let mut cx = Context::new();
        let options = crate::ParseOptions::width(Width::W64);
        let shifted = cx.parse(text, &options).unwrap();
        let nonzero = cx.parse("h >>u 60 != 0", &options).unwrap();
        let mut assumptions = Assumptions::new();
        let id = assumptions.assume_true(&mut cx, nonzero).unwrap();
        let (conditional, reliance) = cx.facts_under(shifted, &assumptions).unwrap().unwrap();
        assert_eq!(conditional.urange.lo().to_u64(), Some(15 << 13));
        assert_eq!(conditional.urange.hi().to_u64(), Some((1 << 28) - 1));
        assert!(reliance.may_use(id));
        for selector in 1..16u64 {
            for high in [selector << 28, ((selector + 1) << 28) - 1] {
                let h = high << 32;
                let scalar = high >> selector;
                let model = [(
                    SymbolKey::from("h"),
                    BitVec::wrapping_from_u64(Width::W64, h),
                )];
                let actual = cx.eval(&[shifted], &model[..]).unwrap()[0];
                assert_eq!(actual.to_u64(), Some(scalar));
                assert!(conditional.contains(&actual));
            }
        }
        let mut zero = Assumptions::new();
        zero.assume_false(&mut cx, nonzero).unwrap();
        assert_eq!(
            cx.facts_with(shifted, &zero)
                .unwrap()
                .unwrap()
                .urange
                .lo()
                .to_u64(),
            Some(0)
        );
        assert_eq!(cx.facts(shifted).unwrap().urange.lo().to_u64(), Some(0));

        let changing = cx.parse(&text.replace("& 63", "& 7"), &options).unwrap();
        let model = [(
            SymbolKey::from("h"),
            BitVec::wrapping_from_u64(Width::W64, 8 << 60),
        )];
        let actual = cx.eval(&[changing], &model[..]).unwrap()[0];
        assert_eq!(actual.to_u64(), Some(1 << 31));
        assert!(
            cx.facts_with(changing, &assumptions)
                .unwrap()
                .unwrap()
                .contains(&actual)
        );
    }
}

#[cfg(feature = "prove")]
#[test]
fn conditional_selector_bounds_prove_without_search_and_keep_scope() {
    use crate::prove::{Config, Limits, Outcome, Question};

    for text in [
        "(h >>u 32) >>u ((h >>u 60) & 63)",
        "h >>u (32 + ((h >>u 60) & 63))",
    ] {
        let mut cx = Context::new();
        let options = crate::ParseOptions::width(Width::W64);
        let shifted = cx.parse(text, &options).unwrap();
        let nonzero = cx.parse("h >>u 60 != 0", &options).unwrap();
        let minimum = cx.constant_u64(Width::W64, 15 << 13).unwrap();
        let claim = cx.cmp(CmpOp::Ule, minimum, shifted).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, nonzero).unwrap();
        let cfg = Config::default().with_samples(0);
        let mut question = Question::valid_under(&mut cx, claim, Some(&assumptions), &cfg).unwrap();
        assert!(matches!(
            question
                .solve(
                    &mut cx,
                    Limits {
                        conflicts: 0,
                        propagations: 0
                    }
                )
                .unwrap(),
            Outcome::Proved(None)
        ));
        assert_eq!(question.stats().nodes, 0);

        // Certificate mode proves the original conditional predicate through
        // its circuit, rather than admitting the word-fact result as a premise.
        let mut checked = Question::valid_under(
            &mut cx,
            claim,
            Some(&assumptions),
            &cfg.with_certificate(true),
        )
        .unwrap();
        let Outcome::Proved(Some(cert)) = checked.solve(&mut cx, Limits::conflicts(1000)).unwrap()
        else {
            panic!("the conditional interval must have an independent original-CNF proof");
        };
        cert.check().unwrap();

        // The same claim fails with a zero selector. Reuse the context to
        // exercise both fact-overlay and simplifier-memo scope changes.
        let mut zero = Assumptions::new();
        zero.assume_false(&mut cx, nonzero).unwrap();
        let mut outside = Question::valid_under(&mut cx, claim, Some(&zero), &cfg).unwrap();
        let Outcome::Refuted(model) = outside.solve(&mut cx, Limits::conflicts(1000)).unwrap()
        else {
            panic!("a conditional lower bound must not escape its nonzero-selector scope");
        };
        assert!(cx.eval(&[nonzero], &model[..]).unwrap()[0].is_zero());
        assert!(cx.eval(&[claim], &model[..]).unwrap()[0].is_zero());
    }
}

#[test]
fn odd_products_preserve_nonzero_values_and_conditional_scope() {
    for bits in [1, 8, 32, 64, 65, 129, 512] {
        let w = width(bits);
        let mut cx = Context::new();
        let x = cx.symbol("x", w).unwrap();
        let y = cx.symbol("y", w).unwrap();
        let p = cx.mul(x, y).unwrap();
        let nonzero = Facts::new(
            KnownBits::unknown(w),
            URange::new(BitVec::one(w), BitVec::ones(w)).unwrap(),
            SRange::full(w),
        )
        .unwrap();
        let odd = Facts::from_known(KnownBits::new(BitVec::zero(w), BitVec::one(w)).unwrap());
        for swapped in [false, true] {
            let (input, multiplier) = if swapped { (y, x) } else { (x, y) };
            let mut both = Assumptions::new();
            let input_id = both.assume(&mut cx, input, nonzero).unwrap();
            let odd_id = both.assume(&mut cx, multiplier, odd).unwrap();
            let proof = cx.prove_under(Query::IsNonZero(p), &both).unwrap();
            assert_eq!(proof.truth, Truth::True, "width={bits}, swapped={swapped}");
            assert!(proof.relies_on.may_use(input_id));
            assert!(proof.relies_on.may_use(odd_id));
            if bits > 1 {
                for keep_odd in [false, true] {
                    let mut partial = Assumptions::new();
                    if keep_odd {
                        partial.assume(&mut cx, multiplier, odd).unwrap();
                    } else {
                        partial.assume(&mut cx, input, nonzero).unwrap();
                    }
                    assert_eq!(
                        cx.prove_with(Query::IsNonZero(p), &partial).unwrap(),
                        Truth::Unknown
                    );
                }
            }
            let mut zero = Assumptions::new();
            zero.assume(&mut cx, input, Facts::constant(&BitVec::zero(w)))
                .unwrap();
            zero.assume(&mut cx, multiplier, odd).unwrap();
            assert_eq!(cx.prove_with(Query::IsZero(p), &zero).unwrap(), Truth::True);
        }
        assert_eq!(cx.prove(Query::IsNonZero(p)).unwrap(), Truth::Unknown);

        if bits > 1 {
            let high = known::bv_shl(&BitVec::one(w), u32::from(bits - 1));
            let even = Facts::constant(&BitVec::wrapping_from_u64(w, 2));
            let result = Facts::apply_bin(BinOp::Mul, &Facts::constant(&high), &even).unwrap();
            assert_eq!(result.as_constant(), Some(BitVec::zero(w)));
        }
    }

    // Exercise the public transfer over complete independent small domains,
    // including even factors and strided nonzero inputs.
    for bits in 1..=6 {
        let w = width(bits);
        let maximum = (1u64 << bits) - 1;
        for stride in [1, 2, 3, 4] {
            let Some(u) = URange::strided(BitVec::one(w), BitVec::ones(w), stride) else {
                continue;
            };
            let input = Facts::new(KnownBits::unknown(w), u, SRange::full(w)).unwrap();
            for parity in [0, 1] {
                let factor = Facts::from_known(
                    KnownBits::new(
                        BitVec::wrapping_from_u64(w, 1 - parity),
                        BitVec::wrapping_from_u64(w, parity),
                    )
                    .unwrap(),
                );
                for swapped in [false, true] {
                    let output = if swapped {
                        Facts::apply_bin(BinOp::Mul, &factor, &input)
                    } else {
                        Facts::apply_bin(BinOp::Mul, &input, &factor)
                    }
                    .unwrap();
                    if parity == 1 {
                        assert!(!output.contains(&BitVec::zero(w)));
                    }
                    for x in 1..=maximum {
                        if !input.contains(&BitVec::wrapping_from_u64(w, x)) {
                            continue;
                        }
                        for y in (parity..=maximum).step_by(2) {
                            let actual = BitVec::wrapping_from_u64(w, x * y);
                            assert!(output.contains(&actual));
                        }
                    }
                }
            }
        }
    }
}

#[test]
fn positive_logical_xorshifts_preserve_nonzero_and_keep_scope() {
    for bits in [1, 8, 32, 64, 65, 129, 512] {
        let w = width(bits);
        let options = crate::ParseOptions::width(w);
        let mut cx = Context::new();
        let nonzero = cx.parse("x != 0", &options).unwrap();
        let mut assumptions = Assumptions::new();
        let id = assumptions.assume_true(&mut cx, nonzero).unwrap();
        for text in [
            "x ^ (x >>u 1)",
            "(x >>u 1) ^ x",
            "x ^ ((x >>u 1) >>u n)",
            "x ^ (x >>u (n | 1))",
            "x ^ (x >>u (1 + (x >>u 1)))",
        ] {
            let expression = cx.parse(text, &options).unwrap();
            let proof = cx
                .prove_under(Query::IsNonZero(expression), &assumptions)
                .unwrap();
            assert_eq!(proof.truth, Truth::True, "width={bits}: {text}");
            assert!(proof.relies_on.may_use(id));
            // A positive count does not justify nonzero without a nonzero source.
            let facts = cx.facts(expression).unwrap();
            assert!(facts.contains(&BitVec::zero(w)));
            let mut zero = Assumptions::new();
            zero.assume_false(&mut cx, nonzero).unwrap();
            assert_eq!(
                cx.prove_with(Query::IsZero(expression), &zero).unwrap(),
                Truth::True
            );
        }
        for text in ["x ^ (x >>u n)", "x ^ (x >>s 1)", "x ^ (y >>u 1)"] {
            let expression = cx.parse(text, &options).unwrap();
            let (x, y, n) = (BitVec::ones(w), BitVec::ones(w), BitVec::zero(w));
            let model = [
                (SymbolKey::from("x"), x),
                (SymbolKey::from("y"), y),
                (SymbolKey::from("n"), n),
            ];
            let actual = cx.eval(&[expression], &model[..]).unwrap()[0];
            assert!(
                cx.facts_with(expression, &assumptions)
                    .unwrap()
                    .unwrap()
                    .contains(&actual)
            );
            if text != "x ^ (y >>u 1)" {
                assert!(actual.is_zero());
                assert_ne!(
                    cx.prove_with(Query::IsNonZero(expression), &assumptions)
                        .unwrap(),
                    Truth::True
                );
            }
        }
    }

    // Every value and variable count of small words, with source-dependent
    // count expressions and a saturating count wider than the data width.
    for bits in 1..=6 {
        let w = width(bits);
        let mut cx = Context::new();
        let options = crate::ParseOptions::width(w);
        let predicate = cx.parse("x != 0", &options).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, predicate).unwrap();
        for text in [
            "x ^ (x >>u (n | 1))",
            "x ^ ((x >>u 1) >>u n)",
            "x ^ (x >>u (1 + (x >>u 1)))",
            "x ^ (x >>u (n + 1))",
        ] {
            let expression = cx.parse(text, &options).unwrap();
            let facts = cx.facts_with(expression, &assumptions).unwrap().unwrap();
            for x in 1..1u64 << bits {
                for n in 0..1u64 << bits {
                    let model = [
                        (SymbolKey::from("x"), BitVec::wrapping_from_u64(w, x)),
                        (SymbolKey::from("n"), BitVec::wrapping_from_u64(w, n)),
                    ];
                    let actual = cx.eval(&[expression], &model[..]).unwrap()[0];
                    assert!(
                        facts.contains(&actual),
                        "width={bits}: {text}, x={x}, n={n}"
                    );
                }
            }
        }
    }
}

#[test]
fn xorshift_nonzero_facts_do_not_admit_wrapping_counts_or_unrelated_sources() {
    for bits in [2, 8, 64, 65, 129, 512] {
        let w = width(bits);
        let options = crate::ParseOptions::width(w);
        let mut cx = Context::new();
        let nonzero = cx.parse("x != 0", &options).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, nonzero).unwrap();
        // The count's own assumption is not a global premise. Dropping it
        // must restore the model with zero count in the same context.
        let count_nonzero = cx.parse("n != 0", &options).unwrap();
        let mut conditional = assumptions.clone();
        conditional.assume_true(&mut cx, count_nonzero).unwrap();
        let general = cx.parse("x ^ (x >>u n)", &options).unwrap();
        let _ = cx.facts_with(general, &conditional).unwrap();
        for (text, x, y, n) in [
            (
                "x ^ (x >>u n)",
                BitVec::one(w),
                BitVec::zero(w),
                BitVec::zero(w),
            ),
            (
                "x ^ (x >>u (n + 1))",
                BitVec::one(w),
                BitVec::zero(w),
                BitVec::ones(w),
            ),
            (
                "x ^ (x >>u (1 + (x >>u 0)))",
                BitVec::ones(w),
                BitVec::zero(w),
                BitVec::zero(w),
            ),
            (
                "x ^ (y >>u 1)",
                BitVec::one(w),
                BitVec::wrapping_from_u64(w, 2),
                BitVec::zero(w),
            ),
            (
                "x ^ (x >>s 1)",
                BitVec::ones(w),
                BitVec::zero(w),
                BitVec::zero(w),
            ),
        ] {
            let expression = cx.parse(text, &options).unwrap();
            let model = [
                (SymbolKey::from("x"), x),
                (SymbolKey::from("y"), y),
                (SymbolKey::from("n"), n),
            ];
            assert!(cx.eval(&[expression], &model[..]).unwrap()[0].is_zero());
            assert!(
                cx.facts_with(expression, &assumptions)
                    .unwrap()
                    .unwrap()
                    .contains(&BitVec::zero(w))
            );
            assert_ne!(
                cx.prove_with(Query::IsNonZero(expression), &assumptions)
                    .unwrap(),
                Truth::True
            );
        }

        // With no fact allowance the correlation matcher cannot walk a DAG
        // on its own to establish a nonzero source or count.
        let mut capped = Context::with_config(crate::ContextConfig::default().with_fact_work(0));
        let expression = capped.parse("(x | 1) ^ ((x | 1) >>u 1)", &options).unwrap();
        assert_eq!(
            capped.prove(Query::IsNonZero(expression)).unwrap(),
            Truth::Unknown
        );
    }
}

#[cfg(feature = "prove")]
#[test]
fn zero_preserving_facts_avoid_circuits_and_have_original_cnf_certificates() {
    use crate::prove::{Config, Limits, Outcome, Question};

    for (bits, text) in [
        (8, "x * (y | 1)"),
        (64, "x * (y | 1)"),
        (65, "x * (y | 1)"),
        (8, "x ^ (x >>u 1)"),
        (65, "x ^ (x >>u 1)"),
        (64, "x ^ ((x >>u 32) >>u (x >>u 60))"),
        (64, "x ^ (x >>u (32 + (x >>u 60)))"),
    ] {
        let mut cx = Context::new();
        let options = crate::ParseOptions::width(width(bits));
        let expression = cx.parse(text, &options).unwrap();
        let source = cx.parse("x != 0", &options).unwrap();
        let zero = cx.zero(width(bits)).unwrap();
        let claim = cx.ne(expression, zero).unwrap();
        let mut assumptions = Assumptions::new();
        assumptions.assume_true(&mut cx, source).unwrap();
        let cfg = Config::default().with_samples(0);
        let mut q = Question::valid_under(&mut cx, claim, Some(&assumptions), &cfg).unwrap();
        assert!(
            matches!(
                q.solve(
                    &mut cx,
                    Limits {
                        conflicts: 0,
                        propagations: 0
                    }
                )
                .unwrap(),
                Outcome::Proved(None)
            ),
            "width={bits}: {text}"
        );
        assert_eq!(q.stats().nodes, 0);

        let mut checked = Question::valid_under(
            &mut cx,
            claim,
            Some(&assumptions),
            &cfg.with_certificate(true),
        )
        .unwrap();
        let Outcome::Proved(Some(cert)) = checked.solve(&mut cx, Limits::conflicts(1000)).unwrap()
        else {
            panic!("expected an original-CNF certificate: width={bits}: {text}");
        };
        cert.check().unwrap();

        let mut outside = Question::valid(&mut cx, claim, &cfg).unwrap();
        let Outcome::Refuted(model) = outside.solve(&mut cx, Limits::conflicts(1000)).unwrap()
        else {
            panic!("zero source must refute the unconditional claim: {text}");
        };
        assert!(
            cx.eval(&[claim, source], &model[..])
                .unwrap()
                .iter()
                .all(BitVec::is_zero)
        );
    }
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

#[test]
fn self_shifts_bound_their_range() {
    // `(b >>u j) >>u (b >>u m)` and `a >>u (a >>u k)` at every width to 7, every `j <= m`,
    // with the base narrowed by masks and offsets so the shifted value's range varies too:
    // every value lies in the facts.
    for w in 1..=7u16 {
        let o = crate::ParseOptions::width(width(w));
        let mut cx = Context::new();
        let wm = (1u64 << w) - 1;
        let bases = [
            "x".to_string(),
            format!("x & {}", 0x55 & wm),
            format!("x | {}", 1u64 << (w - 1)),
            format!("(x & {}) + 1", wm >> 1),
        ];
        for base in &bases {
            for j in 0..w {
                for m in j..w {
                    let src = format!("let b = {base}; (b >>u {j}) >>u (b >>u {m})");
                    let e = cx.parse(&src, &o).unwrap();
                    let src2 = format!("let a = {base} >>u {j}; a >>u (a >>u {})", m - j);
                    let e2 = cx.parse(&src2, &o).unwrap();
                    for e in [e, e2] {
                        let f = cx.facts(e).unwrap();
                        for v in 0..=wm {
                            let env: HashMap<SymbolKey, BitVec> =
                                [(SymbolKey::from("x"), BitVec::wrapping_from_u64(width(w), v))]
                                    .into_iter()
                                    .collect();
                            let r = cx.eval(&[e], &env).unwrap()[0];
                            assert!(f.contains(&r), "{}: {r} not in {f:?}", cx.display(e));
                        }
                    }
                }
            }
        }
    }
    // The mixer's data-dependent shift changes only bits 0 to 27 (the count's range alone
    // allows 32 bits), and exactly those: bit 27 can be set.
    let mut cx = Context::new();
    let o = crate::ParseOptions::width(width(64));
    let g = cx.parse("(h >>u 32) >>u (h >>u 60)", &o).unwrap();
    let f = cx.facts(g).unwrap();
    assert_eq!(f.urange().hi().to_u64(), Some((1 << 28) - 1));
    let h = BitVec::wrapping_from_u64(width(64), 0x0fff_ffff_ffff_ffff);
    let env: HashMap<SymbolKey, BitVec> = [(SymbolKey::from("h"), h)].into_iter().collect();
    assert_eq!(cx.eval(&[g], &env).unwrap()[0].to_u64(), Some(0x0fff_ffff));
}

#[test]
fn self_shifts_with_constant_count_offsets_are_sound_including_wrapping_counts() {
    for bits in 1..=7u16 {
        let w = width(bits);
        let o = crate::ParseOptions::width(w);
        let mut cx = Context::new();
        let maximum = (1u64 << bits) - 1;
        for j in 0..bits {
            for m in j..bits {
                let top_max = maximum >> m;
                let mut offsets = vec![0, 1, u64::from(bits) & maximum, maximum, maximum - top_max];
                if maximum - top_max < maximum {
                    offsets.push(maximum - top_max + 1);
                }
                offsets.sort_unstable();
                offsets.dedup();
                for offset in offsets {
                    let e = cx
                        .parse(&format!("(x >>u {j}) >>u ({offset} + (x >>u {m}))"), &o)
                        .unwrap();
                    let f = cx.facts(e).unwrap();
                    for x in 0..=maximum {
                        let shifted = x >> j;
                        let count = (offset + (x >> m)) & maximum;
                        let expected = if count >= u64::from(bits) {
                            0
                        } else {
                            shifted >> count
                        };
                        assert!(
                            f.contains(&BitVec::wrapping_from_u64(w, expected)),
                            "bits={bits}, j={j}, m={m}, offset={offset}, x={x}, facts={f:?}"
                        );
                    }
                }
            }
        }
    }
    let mut cx = Context::new();
    let o = crate::ParseOptions::width(Width::W64);
    for spelling in ["(h >>u 32) >>u (h >>u 60)", "h >>u (32 + (h >>u 60))"] {
        let shifted = cx.parse(spelling, &o).unwrap();
        let facts = cx.facts(shifted).unwrap();
        assert_eq!(facts.urange().hi().to_u64(), Some((1 << 28) - 1));
        assert_eq!(
            facts.known().known_zero().to_u64(),
            Some(!((1u64 << 28) - 1))
        );
    }
    for (bits, offset, top) in [(65u16, 32u32, 61u32), (129, 64, 125), (512, 256, 508)] {
        let mut cx = Context::new();
        let w = width(bits);
        let o = crate::ParseOptions::width(w);
        let shifted = cx
            .parse(&format!("h >>u ({offset} + (h >>u {top}))"), &o)
            .unwrap();
        assert_eq!(
            cx.facts(shifted).unwrap().urange().hi(),
            known::low_mask(w, top - offset)
        );
    }
}

#[test]
fn self_shift_bounds_through_redundant_count_masks() {
    let mut cx = Context::new();
    let options = crate::ParseOptions::width(Width::W64);
    let bound = (1u64 << 28) - 1;
    for spelling in [
        "(h >>u 32) >>u ((h >>u 60) & 63)",
        "h >>u (32 + ((h >>u 60) & 63))",
        "h >>u ((32 + (h >>u 60)) & 63)",
        "(h >>u 32) >>u (((h >>u 60) & 63) & 15)",
    ] {
        let shifted = cx.parse(spelling, &options).unwrap();
        let facts = cx.facts(shifted).unwrap();
        assert_eq!(facts.urange().hi().to_u64(), Some(bound), "{spelling}");
        assert_eq!(facts.known().known_zero().to_u64(), Some(!bound));
        assert_eq!(
            cx.prove(Query::FitsUnsigned {
                e: shifted,
                bits: 28,
            })
            .unwrap(),
            Truth::True
        );
    }

    // Clearing a possible selector bit changes the count, so this mask cannot be
    // stripped. In particular selector 8 becomes 0 and permits a 32-bit result.
    let shifted = cx
        .parse("(h >>u 32) >>u ((h >>u 60) & 7)", &options)
        .unwrap();
    let wide = BitVec::from_u64(Width::W64, 0x8fff_ffff).unwrap();
    assert!(cx.facts(shifted).unwrap().contains(&wide));
    assert_ne!(
        cx.prove(Query::FitsUnsigned {
            e: shifted,
            bits: 28,
        })
        .unwrap(),
        Truth::True
    );

    // A base declaration can make the same mask redundant. Withdrawing the
    // declaration must also withdraw the tighter bound from the base cache.
    let h = cx.find_symbol(&SymbolKey::from("h")).unwrap();
    cx.declare_known(
        h,
        KnownBits::new(
            BitVec::from_u64(Width::W64, 1 << 63).unwrap(),
            BitVec::zero(Width::W64),
        )
        .unwrap(),
    )
    .unwrap();
    assert_eq!(
        cx.facts(shifted).unwrap().urange().hi().to_u64(),
        Some(bound)
    );
    cx.declare_known(h, KnownBits::unknown(Width::W64)).unwrap();
    assert!(cx.facts(shifted).unwrap().contains(&wide));

    for (bits, offset, top) in [(65u16, 32u32, 61u32), (129, 64, 125), (512, 256, 508)] {
        let mut cx = Context::new();
        let w = width(bits);
        let options = crate::ParseOptions::width(w);
        let count_mask = offset * 2 - 1;
        for spelling in [
            format!("(h >>u {offset}) >>u ((h >>u {top}) & 63)"),
            format!("h >>u ({offset} + ((h >>u {top}) & 63))"),
            format!("h >>u (({offset} + (h >>u {top})) & {count_mask})"),
        ] {
            let shifted = cx.parse(&spelling, &options).unwrap();
            assert_eq!(
                cx.facts(shifted).unwrap().urange().hi(),
                known::low_mask(w, top - offset)
            );
        }
    }
    let w = Width::new(512).unwrap();
    let mut cx = Context::new();
    let shifted = cx
        .parse(
            "h >>u ((256 + (h >>u 508)) & 63)",
            &crate::ParseOptions::width(w),
        )
        .unwrap();
    // This mask removes the offset's set bit, making the actual count 15 at h = -1.
    let actual = known::bv_lshr(&BitVec::ones(w), 15);
    assert!(cx.facts(shifted).unwrap().contains(&actual));
    assert_ne!(
        cx.prove(Query::FitsUnsigned {
            e: shifted,
            bits: 252,
        })
        .unwrap(),
        Truth::True
    );
}

#[test]
fn masked_self_shift_counts_are_sound_including_nonredundant_and_wrapping_cases() {
    for bits in 1..=6u16 {
        let w = width(bits);
        let maximum = (1u64 << bits) - 1;
        let options = crate::ParseOptions::width(w);
        let mut cx = Context::new();
        for m in 0..bits {
            for j in 0..=m {
                let mut masks = vec![0, 1, maximum >> m, maximum, maximum ^ 1];
                masks.sort_unstable();
                masks.dedup();
                for mask in masks {
                    for offset in [0, 1, maximum] {
                        for before_add in [false, true] {
                            let count = if before_add {
                                format!("((x >>u {m}) & {mask}) + {offset}")
                            } else {
                                format!("((x >>u {m}) + {offset}) & {mask}")
                            };
                            let expression = cx
                                .parse(&format!("(x >>u {j}) >>u ({count})"), &options)
                                .unwrap();
                            let facts = cx.facts(expression).unwrap();
                            for x in 0..=maximum {
                                let count = if before_add {
                                    (((x >> m) & mask) + offset) & maximum
                                } else {
                                    (((x >> m) + offset) & maximum) & mask
                                };
                                let value = if count >= u64::from(bits) {
                                    0
                                } else {
                                    (x >> j) >> count
                                };
                                assert!(
                                    facts.contains(&BitVec::wrapping_from_u64(w, value)),
                                    "bits={bits}, j={j}, m={m}, mask={mask}, offset={offset}, \
                                     before_add={before_add}, x={x}, facts={facts:?}"
                                );
                            }
                        }
                    }
                }
            }
        }
    }
}

// ----- floating point ----------------------------------------------------------------------------

/// Every floating-point transfer is sound on tiny formats: structured and random operand facts,
/// every member evaluated.
#[test]
fn floating_point_transfers_are_sound() {
    use crate::fp::node::Desc;
    use crate::fp::{FpFormat, FpOp, RoundingMode};
    let mut rng = Rng(0xf10a_7001);
    for (eb, sb) in [(2, 2), (2, 3), (3, 2), (3, 3), (2, 4), (4, 2)] {
        let f = FpFormat::new(eb, sb).unwrap();
        let w = f.width().bits();
        let st = states(&mut rng, w, 60);
        let other = FpFormat::new(if eb == 2 { 3 } else { 2 }, 3).unwrap();
        let pick = |rng: &mut Rng| &st[rng.below(st.len() as u64) as usize];
        for rm in RoundingMode::ALL {
            let unary = [
                FpOp::Sqrt(rm),
                FpOp::RoundToIntegral(rm),
                FpOp::Convert { to: other, rm },
                FpOp::ToSInt(rm, width(3)),
                FpOp::ToUInt(rm, width(4)),
            ];
            for op in unary {
                let d = Desc { op, format: f };
                for a in &st {
                    check_sound(&TOp::Fp(d), &[a]);
                }
            }
            for op in [FpOp::FromSInt(rm), FpOp::FromUInt(rm)] {
                let d = Desc { op, format: f };
                for a in &states(&mut rng, 5, 20) {
                    check_sound(&TOp::Fp(d), &[a]);
                }
            }
            let binary = [
                FpOp::Add(rm),
                FpOp::Mul(rm),
                FpOp::Div(rm),
                FpOp::Rem,
                FpOp::Min,
                FpOp::Max,
                FpOp::Eq,
                FpOp::Lt,
                FpOp::Le,
            ];
            for op in binary {
                let d = Desc { op, format: f };
                for _ in 0..150 {
                    let (a, b) = (pick(&mut rng), pick(&mut rng));
                    check_sound(&TOp::Fp(d), &[a, b]);
                }
            }
            let d = Desc {
                op: FpOp::Fma(rm),
                format: f,
            };
            for _ in 0..50 {
                let (a, b, c) = (pick(&mut rng), pick(&mut rng), pick(&mut rng));
                check_sound(&TOp::Fp(d), &[a, b, c]);
            }
        }
    }
}

/// The known bits of a square contain every square of a value the operand's facts admit:
/// every known-bits pattern at widths 1 to 6.
#[test]
fn square_known_bits_are_sound() {
    let mut rng = Rng(0x5ca7);
    for w in 1..=6u16 {
        for f in states(&mut rng, w, 40) {
            let sq = super::square_known(&f);
            for v in all_values(w) {
                if !f.contains(&v) {
                    continue;
                }
                let p = BitVec::apply_bin(BinOp::Mul, &v, &v).unwrap();
                assert!(sq.contains(&p), "W={w} {f:?}: {v}² = {p} not in {sq:?}");
            }
        }
    }
    // And they are strong: an odd square is 1 modulo 8, bit 1 of any square is 0.
    let w = width(8);
    let odd = Facts::from_known(KnownBits::from_masks(BitVec::zero(w), BitVec::one(w)));
    assert_eq!(
        super::square_known(&odd).known().known_one().limbs()[0] & 7,
        1
    );
    assert_eq!(
        super::square_known(&odd).known().known_zero().limbs()[0] & 7,
        6
    );
    assert_eq!(
        super::square_known(&Facts::top(w))
            .known()
            .known_zero()
            .limbs()[0],
        2
    );
}
