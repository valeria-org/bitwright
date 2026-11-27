//! Invertibility: every claim checked exhaustively at small widths. A layer the analysis
//! accepts must be injective (bijective) at every value of its parameters, a preimage must be
//! the one value mapping to the constant, and a `False` answer must have a witness.

use super::*;
use crate::testutil::{Rng, width};
use crate::{BinOp, CmpOp, Context, Expr, FnEnv, Query, SymbolKey, UnOp};

fn plain() -> Queries<'static> {
    Queries {
        a: None,
        rel: Reliance::NONE,
    }
}

fn val(w: u16, v: u64) -> BitVec {
    BitVec::wrapping_from_u64(width(w), v)
}

/// The value of `e` with each named symbol set.
fn eval(cx: &mut Context, e: Expr, env: &[(&str, BitVec)]) -> BitVec {
    let env = FnEnv(|k: &SymbolKey, _| {
        env.iter()
            .find(|(n, _)| SymbolKey::from(*n) == *k)
            .map(|(_, v)| *v)
    });
    cx.eval(&[e], &env).unwrap()[0]
}

/// A random function of `v` (and of `p`, if given) that is often, but not always, triangular:
/// leaves are `v` shifted either way, `v` itself, `p` and constants, combined by every kind of
/// operator the dependency analysis reads.
fn g_expr(rng: &mut Rng, cx: &mut Context, v: Expr, p: Option<Expr>, w: u16, depth: u32) -> Expr {
    let wd = width(w);
    let k = |cx: &mut Context, x: u64| cx.constant_u64(wd, x % (1 << w.min(63))).unwrap();
    if depth == 0 || rng.chance(1, 4) {
        return match rng.below(8) {
            0 | 1 => {
                let s = k(cx, 1 + rng.below(u64::from(w)));
                cx.bin(BinOp::LShr, v, s).unwrap()
            }
            2 | 3 => {
                let s = k(cx, 1 + rng.below(u64::from(w)));
                cx.bin(BinOp::Shl, v, s).unwrap()
            }
            4 => v,
            5 => match p {
                Some(p) => p,
                None => k(cx, rng.next()),
            },
            _ => k(cx, rng.next()),
        };
    }
    let d = depth - 1;
    let sub = |rng: &mut Rng, cx: &mut Context| g_expr(rng, cx, v, p, w, d);
    match rng.below(14) {
        0 => {
            let a = sub(rng, cx);
            let op = [UnOp::Not, UnOp::Neg, UnOp::BitRev, UnOp::Popcnt][rng.below(4) as usize];
            cx.un(op, a).unwrap()
        }
        1..=6 => {
            let op = [
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
            ][rng.below(6) as usize];
            let a = sub(rng, cx);
            let b = sub(rng, cx);
            cx.bin(op, a, b).unwrap()
        }
        7 | 8 => {
            // A shift or rotation by a constant, or by a count derived from `v`.
            let op = [
                BinOp::Shl,
                BinOp::LShr,
                BinOp::AShr,
                BinOp::RotL,
                BinOp::RotR,
            ][rng.below(5) as usize];
            let a = sub(rng, cx);
            // A count's range matters: a parameter's count can take any value in it.
            let c = match (rng.below(3), p) {
                (0, _) => k(cx, rng.below(u64::from(w) + 1)),
                (1, Some(p)) => {
                    let m = k(cx, rng.below(4));
                    cx.bin(BinOp::And, p, m).unwrap()
                }
                _ => {
                    let s = k(cx, rng.below(u64::from(w)));
                    let m = k(cx, rng.below(4));
                    let t = cx.bin(BinOp::LShr, v, s).unwrap();
                    cx.bin(BinOp::And, t, m).unwrap()
                }
            };
            cx.bin(op, a, c).unwrap()
        }
        9 => {
            // The mixer shape: `(v >>u a) >>u (v >>u b)`.
            let a = k(cx, rng.below(u64::from(w)));
            let b = k(cx, rng.below(u64::from(w)));
            let x = cx.bin(BinOp::LShr, v, a).unwrap();
            let y = cx.bin(BinOp::LShr, v, b).unwrap();
            cx.bin(BinOp::LShr, x, y).unwrap()
        }
        10 => {
            let a = sub(rng, cx);
            let b = sub(rng, cx);
            let c = sub(rng, cx);
            let z = k(cx, 0);
            let cond = cx.cmp(CmpOp::Ult, c, z).unwrap();
            let cond = if rng.chance(1, 2) {
                cond
            } else {
                let t = k(cx, rng.next());
                cx.cmp(CmpOp::Eq, c, t).unwrap()
            };
            cx.select(cond, a, b).unwrap()
        }
        11 if w > 1 => {
            // Through a narrower value and back.
            let a = sub(rng, cx);
            let n = 1 + rng.below(u64::from(w - 1)) as u16;
            let lo = rng.below(u64::from(w - n + 1)) as u16;
            let t = cx.extract(a, lo, width(n)).unwrap();
            if rng.chance(1, 2) {
                cx.zext(t, wd).unwrap()
            } else {
                cx.sext(t, wd).unwrap()
            }
        }
        12 if w > 1 => {
            let a = sub(rng, cx);
            let b = sub(rng, cx);
            let n = 1 + rng.below(u64::from(w - 1)) as u16;
            let h = cx.extract(a, 0, width(w - n)).unwrap();
            let l = cx.extract(b, w - n, width(n)).unwrap();
            cx.concat(h, l).unwrap()
        }
        _ => {
            let a = sub(rng, cx);
            let b = sub(rng, cx);
            let op = [BinOp::UDiv, BinOp::URem, BinOp::UMulHi][rng.below(3) as usize];
            cx.bin(op, a, b).unwrap()
        }
    }
}

/// `v ⊙ g` for a random operator form.
fn tri_node(rng: &mut Rng, cx: &mut Context, v: Expr, g: Expr) -> Expr {
    match rng.below(4) {
        0 => cx.bin(BinOp::Xor, v, g).unwrap(),
        1 => cx.bin(BinOp::Add, v, g).unwrap(),
        2 => cx.bin(BinOp::Sub, v, g).unwrap(),
        _ => cx.bin(BinOp::Sub, g, v).unwrap(),
    }
}

#[test]
fn triangular_layers_are_bijections_and_solve_exactly() {
    let mut rng = Rng(0x7a1a_0001);
    let (mut accepted, mut refused) = (0, 0);
    for i in 0..3000 {
        let w = 1 + (i % 6) as u16;
        let mut cx = Context::new();
        let v = cx.symbol("v", width(w)).unwrap();
        let g = g_expr(&mut rng, &mut cx, v, None, w, 3);
        let n = tri_node(&mut rng, &mut cx, v, g);
        // Sometimes the inner value takes only some values in context (its facts are narrow);
        // the layer must still be a bijection of every value.
        let (hole, m) = if i % 3 == 0 {
            let x = cx.symbol("x", width(w)).unwrap();
            let mask = cx
                .constant_u64(width(w), rng.next() & ((1 << w) - 1))
                .unwrap();
            let h = cx.bin(BinOp::And, x, mask).unwrap();
            (h, cx.substitute(&[n], &[(v, h)]).unwrap()[0])
        } else {
            (v, n)
        };
        let ni = cx.id(m).unwrap();
        let mut o = plain();
        let Some(layer) = solve_layer(&mut cx, &mut o, ni).unwrap() else {
            refused += 1;
            continue;
        };
        if cx.handle(layer.inner) != hole {
            // `g` folded to leave a primitive layer (checked elsewhere).
            continue;
        }
        let image: Vec<BitVec> = (0..1u64 << w)
            .map(|x| eval(&mut cx, n, &[("v", val(w, x))]))
            .collect();
        let mut sorted = image.clone();
        sorted.sort();
        sorted.dedup();
        assert_eq!(
            sorted.len(),
            image.len(),
            "accepted a non-bijective layer: {}",
            cx.display(n)
        );
        for (x, c) in image.iter().enumerate() {
            let got = preimage(&cx, &mut o, ni, &layer, c).unwrap();
            assert_eq!(
                got,
                Some(Some(val(w, x as u64))),
                "{} at {c}",
                cx.display(n)
            );
        }
        if matches!(layer.map, Map::Region(_)) {
            accepted += 1;
        }
    }
    // Neither vacuous nor indiscriminate.
    assert!(accepted > 400, "{accepted} accepted");
    assert!(refused > 400, "{refused} refused");
}

#[test]
fn triangular_layers_cancel_only_when_injective_at_every_parameter() {
    let mut rng = Rng(0x7a1a_0002);
    let mut cancelled = 0;
    for i in 0..2000 {
        let w = 1 + (i % 4) as u16;
        let mut cx = Context::new();
        let (v, u, p) = (
            cx.symbol("v", width(w)).unwrap(),
            cx.symbol("u", width(w)).unwrap(),
            cx.symbol("p", width(w)).unwrap(),
        );
        let g = g_expr(&mut rng, &mut cx, v, Some(p), w, 3);
        let form = rng.below(4);
        let mk = |cx: &mut Context, x: Expr, g: Expr| match form {
            0 => cx.bin(BinOp::Xor, x, g).unwrap(),
            1 => cx.bin(BinOp::Add, x, g).unwrap(),
            2 => cx.bin(BinOp::Sub, x, g).unwrap(),
            _ => cx.bin(BinOp::Sub, g, x).unwrap(),
        };
        let n1 = mk(&mut cx, v, g);
        // The same function of `u`, or (a near miss) not quite: `v` replaced by `u` in `g`
        // only where it is shifted, or by `p`, or another function altogether.
        let gu = match i % 5 {
            0 => {
                let g2 = g_expr(&mut rng, &mut cx, u, Some(p), w, 3);
                if rng.chance(1, 2) {
                    g2
                } else {
                    cx.substitute(&[g2], &[(u, v)]).unwrap()[0]
                }
            }
            1 => cx.substitute(&[g], &[(v, p)]).unwrap()[0],
            2 => {
                // Swap only the shifted occurrences of `v`.
                let mut subs = Vec::new();
                for e in cx.post_order(&[g]).unwrap() {
                    if let Ok(crate::View::Bin(BinOp::LShr | BinOp::Shl, a, b)) = cx.view(e)
                        && a == v
                    {
                        let t = match cx.view(e).unwrap() {
                            crate::View::Bin(op, _, _) => cx.bin(op, u, b).unwrap(),
                            _ => unreachable!(),
                        };
                        subs.push((e, t));
                    }
                }
                cx.substitute(&[g], &subs).unwrap()[0]
            }
            _ => cx.substitute(&[g], &[(v, u)]).unwrap()[0],
        };
        let n2 = mk(&mut cx, u, gu);
        let (i1, i2) = (cx.id(n1).unwrap(), cx.id(n2).unwrap());
        let mut o = plain();
        let Some((a, b)) = cancel_layer(&mut cx, &mut o, i1, i2).unwrap() else {
            continue;
        };
        cancelled += 1;
        let (a, b) = (cx.handle(a), cx.handle(b));
        // `n1 == n2` exactly when `a == b`, at every assignment.
        for pv in 0..1u64 << w {
            for vv in 0..1u64 << w {
                for uv in 0..1u64 << w {
                    let env = [("v", val(w, vv)), ("u", val(w, uv)), ("p", val(w, pv))];
                    let same = eval(&mut cx, n1, &env) == eval(&mut cx, n2, &env);
                    let inner = eval(&mut cx, a, &env) == eval(&mut cx, b, &env);
                    assert_eq!(
                        same,
                        inner,
                        "{} vs {} at v={vv} u={uv} p={pv}",
                        cx.display(n1),
                        cx.display(n2)
                    );
                }
            }
        }
    }
    assert!(cancelled > 250, "{cancelled}");
}

/// Every primitive layer, at every constant parameter and every value, against brute force.
#[test]
fn primitive_layers_solve_exactly() {
    for w in 1..=5u16 {
        let wd = width(w);
        let mut cx = Context::new();
        let v = cx.symbol("v", wd).unwrap();
        let mut nodes: Vec<(Expr, bool)> = Vec::new();
        for kv in 0..1u64 << w {
            let k = cx.constant_u64(wd, kv).unwrap();
            for op in [
                BinOp::Add,
                BinOp::Sub,
                BinOp::Xor,
                BinOp::Mul,
                BinOp::RotL,
                BinOp::RotR,
            ] {
                // Solvable exactly when the map is a bijection: every multiplier but an even
                // one.
                let bij = op != BinOp::Mul || kv & 1 == 1;
                nodes.push((cx.bin(op, v, k).unwrap(), bij));
                if op == BinOp::Sub {
                    nodes.push((cx.bin(op, k, v).unwrap(), true));
                }
            }
            if w < 5 {
                let kn = cx
                    .constant_u64(width(5 - w), kv & ((1 << (5 - w)) - 1))
                    .unwrap();
                nodes.push((cx.concat(v, kn).unwrap(), true));
                nodes.push((cx.concat(kn, v).unwrap(), true));
            }
        }
        for op in [UnOp::Not, UnOp::Neg, UnOp::BitRev] {
            nodes.push((cx.un(op, v).unwrap(), true));
        }
        for to in [w + 1, 8] {
            if to > w {
                nodes.push((cx.zext(v, width(to)).unwrap(), true));
                nodes.push((cx.sext(v, width(to)).unwrap(), true));
            }
        }
        for (n, solvable) in nodes {
            let ni = cx.id(n).unwrap();
            let wn = cx.wid(ni);
            let image: Vec<BitVec> = (0..1u64 << w)
                .map(|x| eval(&mut cx, n, &[("v", val(w, x))]))
                .collect();
            for c in 0..1u64 << wn {
                let c = val(wn, c);
                let mut o = plain();
                let got = solve_eq(&mut cx, &mut o, ni, &c).unwrap();
                let want: Vec<u64> = (0..1u64 << w).filter(|&x| image[x as usize] == c).collect();
                if cx.const_val(ni).is_some() || cx.handle(ni) == v {
                    continue;
                }
                match (&got, want.as_slice()) {
                    (Some(Solved::Eq(x, s)), [one]) => {
                        assert_eq!(cx.handle(*x), v, "{}", cx.display(n));
                        assert_eq!(*s, val(w, *one), "{} == {c}", cx.display(n));
                    }
                    (Some(Solved::Const(false)), []) => {}
                    (None, _) => assert!(!solvable, "{} == {c} not solved", cx.display(n)),
                    _ => panic!("{} == {c}: {got:?}, preimages {want:?}", cx.display(n)),
                }
            }
        }
    }
}

#[test]
fn inverse_of_odd_multipliers() {
    let mut rng = Rng(3);
    for w in [1u16, 2, 7, 8, 63, 64, 65, 127, 128, 129, 256, 511, 512] {
        for _ in 0..20 {
            let limbs: Vec<u64> = (0..8).map(|_| rng.next() | 1).collect();
            let k = BitVec::wrapping_from_limbs(width(w), &limbs);
            let i = mul_inverse(&k).unwrap();
            assert!(BitVec::bin_unchecked(BinOp::Mul, &k, &i) == BitVec::one(width(w)));
            let even = BitVec::bin_unchecked(BinOp::Shl, &k, &BitVec::one(width(w)));
            assert_eq!(mul_inverse(&even), None);
        }
    }
    // The keys of the mixer this was written for.
    for (k, i) in [
        (0x87c3_7b91_1142_53d5_u64, 0xa984_09e8_82ce_4d7d_u64),
        (0xd322_0fb7_8e33_751f, 0xcfcb_c386_7989_c6df),
        (0xfa17_3d6f_19f3_0f7d, 0x2a3c_88ac_d7e9_21d5),
        (0xd703_63ea_b411_220b, 0xfeed_9c08_5b34_d9a3),
        (0xeb00_9e78_8015_7ecb, 0xe1b0_4a3f_069d_76e3),
    ] {
        assert_eq!(mul_inverse(&val(64, k)), Some(val(64, i)));
    }
}

/// `Query::Injective` and `Query::Bijective` on random expressions: every `True` is injective
/// (bijective) at every value of the other symbol, every `False` has a collision.
#[test]
fn invertibility_queries_are_sound() {
    let mut rng = Rng(0x7a1a_0004);
    let mut g = crate::engine::tests::generator(0x7a1a_0005);
    let (mut yes, mut no) = (0, 0);
    for i in 0..3000 {
        let w = 1 + (i % 4) as u16;
        let wd = width(w);
        let mut cx = Context::new();
        let (x, p) = (cx.symbol("x", wd).unwrap(), cx.symbol("p", wd).unwrap());
        // Chains of layers over `x`, with triangular and non-invertible steps, or anything.
        let e = if i % 3 == 0 {
            g.max_w = w;
            let e = g.expr(&mut cx, w, 3).0;
            // Over the generator's symbols: ask about one of them.
            let _ = e;
            let x0 = cx.symbol(format!("v0_{w}").as_str(), wd).unwrap();
            let q = Query::Injective { e, of: x0 };
            let t = cx.prove(q).unwrap();
            check_injective(&mut cx, e, x0, t, &mut yes, &mut no);
            continue;
        } else {
            let mut e = x;
            for _ in 0..1 + rng.below(4) {
                e = match rng.below(6) {
                    0 => {
                        let gg = g_expr(&mut rng, &mut cx, e, Some(p), w, 2);
                        tri_node(&mut rng, &mut cx, e, gg)
                    }
                    1 => {
                        let k = if rng.chance(1, 2) {
                            p
                        } else {
                            cx.constant_u64(wd, rng.next() & ((1 << w) - 1)).unwrap()
                        };
                        let op = [BinOp::Add, BinOp::Xor, BinOp::Mul, BinOp::RotL, BinOp::And]
                            [rng.below(5) as usize];
                        cx.bin(op, e, k).unwrap()
                    }
                    2 => {
                        let op = [UnOp::Not, UnOp::Neg, UnOp::BitRev][rng.below(3) as usize];
                        cx.un(op, e).unwrap()
                    }
                    3 => {
                        // Feeding the input back in (not injective in general).
                        cx.bin(BinOp::Xor, e, x).unwrap()
                    }
                    4 => {
                        // A multiplier proved odd by its facts, not a constant.
                        let one = cx.constant_u64(wd, 1).unwrap();
                        let o = cx.bin(BinOp::Or, p, one).unwrap();
                        cx.bin(BinOp::Mul, e, o).unwrap()
                    }
                    _ => {
                        let k = cx.constant_u64(wd, rng.next() & ((1 << w) - 1)).unwrap();
                        cx.bin(BinOp::Sub, k, e).unwrap()
                    }
                };
            }
            e
        };
        for of in [x, p] {
            let t = cx.prove(Query::Injective { e, of }).unwrap();
            check_injective(&mut cx, e, of, t, &mut yes, &mut no);
            let b = cx.prove(Query::Bijective { e, of }).unwrap();
            if b == Truth::True {
                assert_eq!(t, Truth::True);
                assert_eq!(cx.width(e).unwrap(), cx.width(of).unwrap());
            }
        }
    }
    assert!(yes > 800, "{yes} proved");
    assert!(no > 100, "{no} refuted");
}

/// Checks a `Query::Injective` answer about `e` in `of` (any symbol) exhaustively: with `of`
/// replaced by every value and every other symbol fixed at every value.
fn check_injective(cx: &mut Context, e: Expr, of: Expr, t: Truth, yes: &mut u32, no: &mut u32) {
    if t == Truth::Unknown {
        return;
    }
    let syms = cx.symbols_in(&[e, of]).unwrap();
    let keys: Vec<(SymbolKey, Width)> = syms
        .iter()
        .map(|&s| {
            (
                cx.symbol_key(s).unwrap().clone(),
                cx.symbol_width(s).unwrap(),
            )
        })
        .collect();
    let of_key = keys
        .iter()
        .position(|(k, _)| Some(k) == cx.symbol_id(of).unwrap().and_then(|s| cx.symbol_key(s)))
        .unwrap();
    let wx = keys[of_key].1.bits();
    let others: Vec<usize> = (0..keys.len()).filter(|&i| i != of_key).collect();
    let bits: u32 = others.iter().map(|&i| u32::from(keys[i].1.bits())).sum();
    if bits > 12 {
        return;
    }
    let mut injective_everywhere = true;
    for fixed in 0..1u64 << bits {
        let mut rest = fixed;
        let mut vals: Vec<BitVec> = vec![BitVec::zero(Width::W1); keys.len()];
        for &i in &others {
            let w = keys[i].1.bits();
            vals[i] = BitVec::wrapping_from_u64(keys[i].1, rest & ((1 << w) - 1));
            rest >>= w;
        }
        let mut seen: Vec<BitVec> = Vec::new();
        for xv in 0..1u64 << wx {
            vals[of_key] = BitVec::wrapping_from_u64(keys[of_key].1, xv);
            let env =
                FnEnv(|k: &SymbolKey, _| keys.iter().position(|(kk, _)| kk == k).map(|i| vals[i]));
            seen.push(cx.eval(&[e], &env).unwrap()[0]);
        }
        let n = seen.len();
        seen.sort();
        seen.dedup();
        if seen.len() != n {
            injective_everywhere = false;
            assert_ne!(
                t,
                Truth::True,
                "claimed injective: {} in {}",
                cx.display(e),
                cx.display(of)
            );
        }
    }
    match t {
        Truth::True => *yes += 1,
        Truth::False => {
            assert!(
                !injective_everywhere,
                "refuted an injective {} in {}",
                cx.display(e),
                cx.display(of)
            );
            *no += 1;
        }
        Truth::Unknown => {}
    }
}

/// Every primitive layer on both sides, with the shared operand a constant or a symbol whose
/// facts do or do not make it odd: `n1 == n2` exactly when the cancelled operands are equal.
#[test]
fn primitive_layers_cancel_exactly() {
    for w in 1..=3u16 {
        let wd = width(w);
        let mut cx = Context::new();
        let (v, u, p) = (
            cx.symbol("v", wd).unwrap(),
            cx.symbol("u", wd).unwrap(),
            cx.symbol("p", wd).unwrap(),
        );
        let one = cx.constant_u64(wd, 1).unwrap();
        let mut shared: Vec<Expr> = vec![p, cx.bin(BinOp::Or, p, one).unwrap()];
        shared.push(cx.bin(BinOp::Shl, p, one).unwrap());
        for kv in 0..1u64 << w {
            shared.push(cx.constant_u64(wd, kv).unwrap());
        }
        let mut pairs: Vec<(Expr, Expr)> = Vec::new();
        for &k in &shared {
            for op in BinOp::ALL {
                let (a, b) = (cx.bin(op, v, k).unwrap(), cx.bin(op, u, k).unwrap());
                pairs.push((a, b));
                let (a, b) = (cx.bin(op, k, v).unwrap(), cx.bin(op, k, u).unwrap());
                pairs.push((a, b));
            }
            if w < 3 {
                let kn = cx.constant_u64(width(3 - w), 1).unwrap();
                for (a, b) in [
                    (cx.concat(v, kn).unwrap(), cx.concat(u, kn).unwrap()),
                    (cx.concat(kn, v).unwrap(), cx.concat(kn, u).unwrap()),
                ] {
                    pairs.push((a, b));
                }
            }
        }
        for op in UnOp::ALL {
            if op == UnOp::Bswap {
                continue;
            }
            pairs.push((cx.un(op, v).unwrap(), cx.un(op, u).unwrap()));
        }
        pairs.push((cx.zext(v, width(5)).unwrap(), cx.zext(u, width(5)).unwrap()));
        pairs.push((cx.sext(v, width(5)).unwrap(), cx.sext(u, width(5)).unwrap()));
        let mut cancelled = 0;
        for (n1, n2) in pairs {
            let (i1, i2) = (cx.id(n1).unwrap(), cx.id(n2).unwrap());
            let mut o = plain();
            let Some((a, b)) = cancel_layer(&mut cx, &mut o, i1, i2).unwrap() else {
                continue;
            };
            cancelled += 1;
            let (a, b) = (cx.handle(a), cx.handle(b));
            for pv in 0..1u64 << w {
                for vv in 0..1u64 << w {
                    for uv in 0..1u64 << w {
                        let env = [("v", val(w, vv)), ("u", val(w, uv)), ("p", val(w, pv))];
                        let same = eval(&mut cx, n1, &env) == eval(&mut cx, n2, &env);
                        let inner = eval(&mut cx, a, &env) == eval(&mut cx, b, &env);
                        assert_eq!(same, inner, "{} vs {}", cx.display(n1), cx.display(n2));
                    }
                }
            }
        }
        assert!(cancelled > 20, "{cancelled}");
    }
    // A multiplier that is not proved odd is no layer, and nothing is solved through it.
    let mut cx = Context::new();
    let v = cx.symbol("v", width(8)).unwrap();
    for k in [0u64, 2, 6, 0x80] {
        let kc = cx.constant_u64(width(8), k).unwrap();
        let n = cx.bin(BinOp::Mul, v, kc).unwrap();
        let ni = cx.id(n).unwrap();
        if cx.const_val(ni).is_none() {
            assert!(solve_layer(&mut cx, &mut plain(), ni).unwrap().is_none());
        }
    }
}

/// `compact` from a pointer encoding, scaled to 8 bits (split at bit 5): the low bits are
/// `(x ^ l) + (k - l + d)`, the high bits `(x >> 5) - ((x >> 4) & h)` plus the carry of the low
/// half. Injective in `x` for every parameter value.
fn compact8(x: &str, k: &str, l: &str, c: &str, d: &str, h: &str, shift: u8) -> String {
    format!(
        "(((({x} >>u 5) - (({x} >>u {s}) & {h}) \
           + zext<8>(((({x} ^ {l}) + ({k} - {l} + {c})) & 31) <u {k}) - 1) << 5) \
         | ((({x} ^ {l}) + ({k} - {l} + {d})) & 31))",
        s = 5 - shift
    )
}

#[test]
fn block_triangular_maps_are_recovered() {
    let o = crate::ParseOptions::width(width(8));
    let mut cx = Context::new();
    let x = cx.parse("x", &o).unwrap();
    let f = cx
        .parse(&compact8("x", "k", "l", "c", "d", "h", 1), &o)
        .unwrap();
    assert_eq!(
        cx.prove(Query::Bijective { e: f, of: x }).unwrap(),
        Truth::True
    );
    // The claim, at random parameter values: all 256 inputs have distinct images.
    let mut rng = Rng(0xc0_4ac7);
    for _ in 0..64 {
        let p: Vec<u64> = (0..5).map(|_| rng.below(256)).collect();
        let env = |xv: u64| {
            [
                ("x", val(8, xv)),
                ("k", val(8, p[0])),
                ("l", val(8, p[1])),
                ("c", val(8, p[2])),
                ("d", val(8, p[3])),
                ("h", val(8, p[4])),
            ]
        };
        let mut seen: Vec<BitVec> = (0..256).map(|xv| eval(&mut cx, f, &env(xv))).collect();
        seen.sort();
        seen.dedup();
        assert_eq!(seen.len(), 256, "{p:?}");
    }
    // Without the shift, bit `i` reads bit `i`: not claimed, and not injective.
    let g = cx
        .parse(&compact8("x", "k", "l", "c", "d", "h", 0), &o)
        .unwrap();
    assert_ne!(
        cx.prove(Query::Injective { e: g, of: x }).unwrap(),
        Truth::True
    );
    // Solved at every constant, exactly (parameters fixed).
    let fc = cx
        .parse(
            &compact8("x", "0x9c", "0x35", "0x0e", "0xf1", "0x16", 1),
            &o,
        )
        .unwrap();
    let fi = cx.id(fc).unwrap();
    let image: Vec<BitVec> = (0..256)
        .map(|xv| eval(&mut cx, fc, &[("x", val(8, xv))]))
        .collect();
    for cv in 0..256u64 {
        let c = val(8, cv);
        let want: Vec<u64> = (0..256).filter(|&xv| image[xv as usize] == c).collect();
        match solve_eq(&mut cx, &mut plain(), fi, &c).unwrap() {
            Some(Solved::Eq(v, s)) => {
                assert_eq!(cx.handle(v), x);
                assert_eq!(want, vec![s.to_u64().unwrap()], "{cv:#x}");
            }
            Some(Solved::Const(false)) => assert!(want.is_empty(), "{cv:#x}"),
            other => panic!("{cv:#x}: {other:?}"),
        }
    }
    // Cancelled with the same parameters; with another `h`, not.
    for (hy, cancels) in [("h", true), ("h2", false)] {
        let a = cx
            .parse(&compact8("x", "k", "l", "c", "d", "h", 1), &o)
            .unwrap();
        let b = cx
            .parse(&compact8("y", "k", "l", "c", "d", hy, 1), &o)
            .unwrap();
        let (ia, ib) = (cx.id(a).unwrap(), cx.id(b).unwrap());
        let got = cancel_layer(&mut cx, &mut plain(), ia, ib).unwrap();
        assert_eq!(got.is_some(), cancels, "{hy}");
        if let Some((p, q)) = got {
            assert_eq!(
                (cx.handle(p), cx.handle(q)),
                (x, cx.parse("y", &o).unwrap())
            );
        }
    }
}

/// Random maps of `x` built from pieces that keep a pivot, joined into blocks, with decoys that
/// do not (`x & p`, `f(x) ^ x`, a variable shift, a lossy half).
fn block_expr(rng: &mut Rng, cx: &mut Context, x: Expr, p: Expr, w: u16, depth: u32) -> Expr {
    let wd = width(w);
    let k = |cx: &mut Context, v: u64| cx.constant_u64(wd, v & ((1 << w) - 1)).unwrap();
    if depth == 0 {
        return match rng.below(6) {
            0 => x,
            1 => cx.bin(BinOp::Xor, x, p).unwrap(),
            2 => {
                let c = k(cx, rng.next());
                cx.bin(BinOp::Add, x, c).unwrap()
            }
            3 => {
                let c = k(cx, rng.next() | 1);
                cx.bin(BinOp::Mul, x, c).unwrap()
            }
            4 => cx.bin(BinOp::Sub, p, x).unwrap(),
            _ => cx.un(UnOp::Not, x).unwrap(),
        };
    }
    let d = depth - 1;
    let s = 1 + rng.below(u64::from(w.max(2) - 1)) as u16;
    match rng.below(10) {
        // Two halves: the low `s` bits of one map, the rest from another (disjoint `|`).
        0..=2 if w > 1 => {
            let lo = block_expr(rng, cx, x, p, w, d);
            let hi = block_expr(rng, cx, x, p, w, d);
            let m = k(cx, (1 << s) - 1);
            let lo = cx.bin(BinOp::And, lo, m).unwrap();
            let sc = k(cx, u64::from(s));
            let hi = cx.bin(BinOp::Shl, hi, sc).unwrap();
            let hi = if rng.chance(1, 2) {
                // Carry from the low half into the high half.
                let t = cx.cmp(CmpOp::Ult, lo, p).unwrap();
                let t = cx.zext(t, wd).unwrap();
                let t = cx.bin(BinOp::Shl, t, sc).unwrap();
                cx.bin(BinOp::Add, hi, t).unwrap()
            } else {
                hi
            };
            cx.bin(BinOp::Or, hi, lo).unwrap()
        }
        3 if w > 1 => {
            let a = block_expr(rng, cx, x, p, w, d);
            let b = block_expr(rng, cx, x, p, w, d);
            let h = cx.extract(a, s, width(w - s)).unwrap();
            let l = cx.extract(b, 0, width(s)).unwrap();
            cx.concat(h, l).unwrap()
        }
        4 => {
            // An xorshift or add-shift step.
            let a = block_expr(rng, cx, x, p, w, d);
            let sc = k(cx, u64::from(s));
            let op = [BinOp::LShr, BinOp::Shl][rng.below(2) as usize];
            let t = cx.bin(op, a, sc).unwrap();
            let t = if rng.chance(1, 2) {
                cx.bin(BinOp::And, t, p).unwrap()
            } else {
                t
            };
            let join = [BinOp::Xor, BinOp::Add, BinOp::Sub][rng.below(3) as usize];
            cx.bin(join, a, t).unwrap()
        }
        5 => {
            let a = block_expr(rng, cx, x, p, w, d);
            let b = block_expr(rng, cx, x, p, w, d);
            let z = k(cx, 0);
            let c = cx.cmp(CmpOp::Eq, p, z).unwrap();
            cx.select(c, a, b).unwrap()
        }
        6 => {
            let a = block_expr(rng, cx, x, p, w, d);
            let r = k(cx, rng.below(u64::from(w)));
            cx.bin(BinOp::RotL, a, r).unwrap()
        }
        // Decoys.
        7 => {
            let a = block_expr(rng, cx, x, p, w, d);
            cx.bin(BinOp::And, a, p).unwrap()
        }
        8 => {
            let a = block_expr(rng, cx, x, p, w, d);
            let t = cx.bin(BinOp::LShr, a, p).unwrap();
            cx.bin(BinOp::Xor, a, t).unwrap()
        }
        _ => {
            let a = block_expr(rng, cx, x, p, w, d);
            let b = block_expr(rng, cx, x, p, w, d);
            cx.bin(BinOp::Xor, a, b).unwrap()
        }
    }
}

#[test]
fn regions_are_injective_and_solve_exactly() {
    let mut rng = Rng(0x7a1a_0006);
    let (mut proved, mut solved) = (0, 0);
    for i in 0..2500 {
        let w = 2 + (i % 5) as u16;
        let mut cx = Context::new();
        let (x, p) = (
            cx.symbol("x", width(w)).unwrap(),
            cx.symbol("p", width(w)).unwrap(),
        );
        let depth = 1 + rng.below(3) as u32;
        let e = block_expr(&mut rng, &mut cx, x, p, w, depth);
        let t = cx.prove(Query::Injective { e, of: x }).unwrap();
        if t == Truth::True {
            proved += 1;
            // Injective at every value of `p`.
            for pv in 0..1u64 << w {
                let mut seen: Vec<BitVec> = (0..1u64 << w)
                    .map(|xv| eval(&mut cx, e, &[("x", val(w, xv)), ("p", val(w, pv))]))
                    .collect();
                seen.sort();
                seen.dedup();
                assert_eq!(seen.len(), 1 << w, "{} at p={pv}", cx.display(e));
            }
        }
        // With `p` fixed, solving at every constant is exact.
        let pv = rng.below(1 << w);
        let pc = cx.constant_u64(width(w), pv).unwrap();
        let ec = cx.substitute(&[e], &[(p, pc)]).unwrap()[0];
        let ei = cx.id(ec).unwrap();
        let image: Vec<BitVec> = (0..1u64 << w)
            .map(|xv| eval(&mut cx, ec, &[("x", val(w, xv))]))
            .collect();
        for cv in 0..1u64 << w {
            let c = val(w, cv);
            let got = solve_eq(&mut cx, &mut plain(), ei, &c).unwrap();
            let want: Vec<u64> = (0..1u64 << w)
                .filter(|&xv| image[xv as usize] == c)
                .collect();
            match got {
                None => {}
                Some(Solved::Const(false)) => {
                    assert!(want.is_empty(), "{} == {cv}", cx.display(ec));
                    solved += 1;
                }
                Some(Solved::Eq(v, s)) => {
                    // `v == s` must hold exactly where `ec == c` does.
                    let vh = cx.handle(v);
                    for xv in 0..1u64 << w {
                        let lhs = image[xv as usize] == c;
                        let rhs = eval(&mut cx, vh, &[("x", val(w, xv))]) == s;
                        assert_eq!(lhs, rhs, "{} == {cv} at x={xv}", cx.display(ec));
                    }
                    solved += 1;
                }
                Some(Solved::Const(true)) => panic!("{} == {cv} claimed always", cx.display(ec)),
            }
        }
    }
    assert!(proved > 300, "{proved} proved");
    assert!(solved > 2000, "{solved} solved");
}

/// A random polynomial in `x`: products of values that both vary (`x·x`, `(x << s)·x`,
/// `(x − ~x)·x`, that is `(2x + 1)·x`), sums and differences of them, and constant multiples.
fn poly_expr(rng: &mut Rng, cx: &mut Context, x: Expr, w: u16, depth: u32) -> Expr {
    let wd = width(w);
    if depth == 0 || rng.chance(1, 4) {
        return match rng.below(6) {
            0 | 1 => x,
            2 => {
                let s = cx.constant_u64(wd, 1 + rng.below(2)).unwrap();
                cx.bin(BinOp::Shl, x, s).unwrap()
            }
            3 => cx.bin(BinOp::Add, x, x).unwrap(),
            4 => {
                let n = cx.un(UnOp::Not, x).unwrap();
                cx.bin(BinOp::Sub, x, n).unwrap()
            }
            _ => cx.constant_u64(wd, rng.next() & ((1 << w) - 1)).unwrap(),
        };
    }
    let a = poly_expr(rng, cx, x, w, depth - 1);
    let b = poly_expr(rng, cx, x, w, depth - 1);
    match rng.below(5) {
        0 | 1 => cx.bin(BinOp::Mul, a, b).unwrap(),
        2 => cx.bin(BinOp::Add, a, b).unwrap(),
        3 => cx.bin(BinOp::Sub, a, b).unwrap(),
        _ => {
            let k = cx.constant_u64(wd, rng.next() & ((1 << w) - 1)).unwrap();
            cx.bin(BinOp::Mul, a, k).unwrap()
        }
    }
}

/// Polynomials, permutation polynomials among them (`2x² + x`): every injectivity claim and
/// every solution checked at every value.
#[test]
fn polynomials_are_injective_and_solve_exactly() {
    let mut rng = Rng(0x7a1a_00a1);
    let (mut proved, mut solved) = (0, 0);
    for i in 0..1500 {
        let w = 2 + (i % 7) as u16;
        let mut cx = Context::new();
        let x = cx.symbol("x", width(w)).unwrap();
        let depth = 1 + rng.below(3) as u32;
        let e = poly_expr(&mut rng, &mut cx, x, w, depth);
        let t = cx.prove(Query::Injective { e, of: x }).unwrap();
        let image: Vec<BitVec> = (0..1u64 << w)
            .map(|xv| eval(&mut cx, e, &[("x", val(w, xv))]))
            .collect();
        if t == Truth::True {
            proved += 1;
            let mut seen = image.clone();
            seen.sort();
            seen.dedup();
            assert_eq!(seen.len(), 1 << w, "claimed injective: {}", cx.display(e));
        }
        let ei = cx.id(e).unwrap();
        for _ in 0..4 {
            let c = val(w, rng.below(1 << w));
            match solve_eq(&mut cx, &mut plain(), ei, &c).unwrap() {
                None => {}
                Some(Solved::Const(false)) => {
                    assert!(!image.contains(&c), "{} == {c:?}", cx.display(e));
                    solved += 1;
                }
                Some(Solved::Eq(v, s)) => {
                    let vh = cx.handle(v);
                    for xv in 0..1u64 << w {
                        let lhs = image[xv as usize] == c;
                        let rhs = eval(&mut cx, vh, &[("x", val(w, xv))]) == s;
                        assert_eq!(lhs, rhs, "{} == {c:?} at x={xv}", cx.display(e));
                    }
                    solved += 1;
                }
                Some(Solved::Const(true)) => panic!("{} == {c:?} claimed always", cx.display(e)),
            }
        }
    }
    assert!(proved > 100, "{proved} proved");
    assert!(solved > 400, "{solved} solved");
}

/// A rotation count wider than 64 bits is reduced modulo the width exactly, not saturated:
/// counts from `2^64` up, or from just below it, rotate by 0 at some `y`, where
/// `x ^ (rot(x, count) & m)` is `x & !m`, so it is no layer over `x`.
#[test]
fn wide_rotation_counts_are_not_saturated() {
    let mut cx = Context::new();
    let o = crate::ParseOptions::width(Width::W128);
    let x = cx.parse("x", &o).unwrap();
    for (count, y, m) in [
        // `[2^64, 2^128)`: both bounds saturate.
        (
            "y | 0x10000000000000000",
            0,
            "0x7fffffffffffffffffffffffffffffff",
        ),
        // `[2^64 - 3, 2^64 + 4]`: the high bound saturates.
        (
            "0xfffffffffffffffd + (y & 7)",
            3,
            "0x1fffffffffffffffffffffffffffffff",
        ),
    ] {
        for rot in ["rotl", "rotr"] {
            let src = format!("x ^ ({rot}(x, {count}) & {m})");
            let e = cx.parse(&src, &o).unwrap();
            let at =
                |cx: &mut Context, xv: u64| eval(cx, e, &[("x", val(128, xv)), ("y", val(128, y))]);
            assert_eq!(at(&mut cx, 0), at(&mut cx, 1), "{src} collides at y = {y}");
            let t = cx.prove(Query::Injective { e, of: x }).unwrap();
            assert_ne!(t, Truth::True, "{src}");
        }
    }
}

/// A random affine map over GF(2) of `x`: xors of shifted, rotated, masked, reversed copies.
fn gf2_expr(rng: &mut Rng, cx: &mut Context, x: Expr, w: u16, depth: u32) -> Expr {
    let wd = width(w);
    let k = |cx: &mut Context, v: u64| cx.constant(&BitVec::wrapping_from_u64(wd, v)).unwrap();
    if depth == 0 || rng.chance(1, 4) {
        return x;
    }
    let d = depth - 1;
    let a = gf2_expr(rng, cx, x, w, d);
    match rng.below(9) {
        0 | 1 => {
            let b = gf2_expr(rng, cx, x, w, d);
            cx.bin(BinOp::Xor, a, b).unwrap()
        }
        2 => {
            let s = k(cx, rng.below(u64::from(w)));
            cx.bin(BinOp::RotL, a, s).unwrap()
        }
        3 => {
            let s = k(cx, 1 + rng.below(u64::from(w)));
            cx.bin(BinOp::LShr, a, s).unwrap()
        }
        4 => {
            let s = k(cx, 1 + rng.below(u64::from(w)));
            cx.bin(BinOp::Shl, a, s).unwrap()
        }
        5 => {
            let m = k(cx, rng.next());
            cx.bin(BinOp::And, a, m).unwrap()
        }
        6 => {
            let m = k(cx, rng.next());
            cx.bin(BinOp::Xor, a, m).unwrap()
        }
        7 => cx.un(UnOp::Not, a).unwrap(),
        _ => {
            let s = k(cx, rng.below(u64::from(w)));
            let r = cx.bin(BinOp::RotR, a, s).unwrap();
            cx.bin(BinOp::Xor, r, x).unwrap()
        }
    }
}

/// Affine maps over GF(2): the rank decides injectivity exactly (checked by every input at
/// small widths), `Query::Injective` agrees where it answers, and solving at a constant gives
/// the preimage or proves there is none.
#[test]
fn gf2_maps_are_decided_by_rank() {
    let mut rng = Rng(0x6f2);
    let (mut yes, mut no, mut solved) = (0, 0, 0);
    for i in 0..600 {
        let w = 2 + (i % 7) as u16;
        let mut cx = Context::new();
        let x = cx.symbol("x", width(w)).unwrap();
        let e = gf2_expr(&mut rng, &mut cx, x, w, 4);
        let (ei, xi) = (cx.id(e).unwrap(), cx.id(x).unwrap());
        let nodes: Vec<u32> = cx
            .post_order(&[e])
            .unwrap()
            .into_iter()
            .map(|h| cx.id(h).unwrap())
            .collect();
        let Some(map) = gf2::rows(&cx, xi, &nodes) else {
            continue;
        };
        // Folded to a constant by construction (`x ^ x`).
        let Some(rows) = map.get(&ei).cloned() else {
            continue;
        };
        let full = gf2::rank(&rows) == u32::from(w);
        assert_eq!(gf2::full_rank(&rows, u32::from(w)), full);
        // The truth, by every input.
        let mut seen: Vec<BitVec> = (0..1u64 << w)
            .map(|v| eval(&mut cx, e, &[("x", val(w, v))]))
            .collect();
        seen.sort();
        seen.dedup();
        assert_eq!(full, seen.len() == 1 << w, "{}", cx.display(e));
        let t = cx.prove(Query::Injective { e, of: x }).unwrap();
        check_injective(&mut cx, e, x, t, &mut yes, &mut no);
        // Preimages through the engine's solver: e == c.
        let c = val(w, rng.next());
        let f0 = eval(&mut cx, e, &[("x", val(w, 0))]);
        let y: Vec<bool> = (0..w).map(|k| c.bit(k) != f0.bit(k)).collect();
        match gf2::solve(&rows, &y, u32::from(w)) {
            Some(Some(v)) => {
                assert_eq!(eval(&mut cx, e, &[("x", val(w, v[0]))]), c);
                solved += 1;
            }
            Some(None) => {
                assert!(!seen.contains(&c));
            }
            None => assert!(!full),
        }
    }
    eprintln!("gf2: {yes} injective, {no} refuted, {solved} solved");
    assert!(yes > 50 && solved > 50, "{yes} {no} {solved}");
}

#[test]
fn wide_gf2_bijection_and_preimage_up_to_512_bits() {
    use crate::ParseOptions;
    use crate::engine::Engine;
    for &bits in &[160u16, 256, 384, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        let mut cx = Context::new();
        let s1 = bits / 3;
        let s2 = bits / 5 + 7;
        let r1 = bits / 7 + 3;
        let src = format!(
            "let y = x ^ (x >>u {s1}); let z = y ^ (y << {s2}); rotl(z, {r1}) ^ 0x13579bdf"
        );
        let e = cx.parse(&src, &o).unwrap();
        let x = cx.parse("x", &o).unwrap();
        assert_eq!(
            cx.prove(Query::Bijective { e, of: x }).unwrap(),
            Truth::True,
            "width {bits}"
        );
        // Solve `e == target` at a concrete point and verify `e(preimage) == target`.
        let mut limbs = [0u64; 8];
        for (i, l) in limbs.iter_mut().enumerate() {
            *l = 0x9E37_79B9_7F4A_7C15u64.wrapping_mul((i as u64) + 1);
        }
        let secret = BitVec::wrapping_from_limbs(w, &limbs);
        let target = eval(&mut cx, e, &[("x", secret)]);
        let tc = cx.constant(&target).unwrap();
        let eq = cx.cmp(crate::CmpOpExt::Eq, e, tc).unwrap();
        let simp = Engine::standard().simplify(&mut cx, eq).unwrap().expr;
        let sc = cx.constant(&secret).unwrap();
        let want = cx.cmp(crate::CmpOpExt::Eq, x, sc).unwrap();
        assert_eq!(simp, want, "width {bits}: {}", cx.display(simp));
    }
}

#[test]
fn hole_mask_operations_across_512_bits() {
    assert!(HoleMask::ZERO.is_zero());
    assert_eq!(HoleMask::ZERO.count_ones(), 0);
    assert_eq!(HoleMask::ZERO.first_one(), None);

    for b in [0u16, 1, 63, 64, 65, 127, 128, 191, 255, 256, 383, 510, 511] {
        let m = HoleMask::single(b);
        assert!(!m.is_zero());
        assert!(m.test(b));
        assert!(!m.test(b.wrapping_add(1) % 512));
        assert_eq!(m.count_ones(), 1);
        assert_eq!(m.first_one(), Some(b));
        let mut c = m;
        c.clear(b);
        assert!(c.is_zero());
    }
    assert!(HoleMask::single(512).is_zero());

    for n in [0u16, 1, 7, 63, 64, 65, 128, 256, 511, 512] {
        let low = HoleMask::low_ones(n);
        assert_eq!(low.count_ones(), u32::from(n));
        assert_eq!(low.first_one(), (n > 0).then_some(0));
        for b in [0u16, 63, 64, 127, 128, 255, 256, 510, 511] {
            assert_eq!(low.test(b), b < n);
        }
    }

    let a = HoleMask::single(5) | HoleMask::single(300);
    let b = HoleMask::single(300) | HoleMask::single(511);
    assert_eq!((a & b), HoleMask::single(300));
    assert_eq!((a ^ b), HoleMask::single(5) | HoleMask::single(511));
    let mut x = a;
    x |= b;
    assert_eq!(x.count_ones(), 3);
    x &= !HoleMask::single(5);
    assert_eq!(x.first_one(), Some(300));
    x ^= HoleMask::single(300);
    assert_eq!(x, HoleMask::single(511));
}

fn deterministic_wide(w: Width, seed: u64) -> BitVec {
    let mut rng = Rng(seed);
    let mut limbs = [0u64; 8];
    for l in &mut limbs {
        *l = rng.next();
    }
    BitVec::wrapping_from_limbs(w, &limbs)
}

#[test]
fn wide_pivot_regions_256_and_512_bits() {
    use crate::ParseOptions;

    // 1. Xorshift involutions and variable-shift mixers at 256 and 512 bits.
    for (bits, expr_src, cancel_rhs) in [
        (256u16, "h ^ (h >>u 128)", "g ^ (g >>u 128)"),
        (
            256,
            "h ^ ((h >>u 96) >>u (h >>u 252))",
            "g ^ ((g >>u 96) >>u (g >>u 252))",
        ),
        (
            512,
            "h ^ (h >>u 200) ^ (h >>u 400)",
            "g ^ (g >>u 200) ^ (g >>u 400)",
        ),
        (
            512,
            "h ^ ((h >>u 200) >>u (h >>u 508))",
            "g ^ ((g >>u 200) >>u (g >>u 508))",
        ),
    ] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        let mut cx = Context::new();
        let h = cx.parse("h", &o).unwrap();
        let g = cx.parse("g", &o).unwrap();
        let e1 = cx.parse(expr_src, &o).unwrap();
        let e2 = cx.parse(cancel_rhs, &o).unwrap();

        assert_eq!(
            cx.prove(Query::Bijective { e: e1, of: h }).unwrap(),
            Truth::True,
            "{expr_src} @ {bits}"
        );
        assert_eq!(
            cx.prove(Query::Injective { e: e1, of: h }).unwrap(),
            Truth::True,
            "{expr_src} @ {bits}"
        );

        let (i1, i2) = (cx.id(e1).unwrap(), cx.id(e2).unwrap());
        let cancelled = cancel_layer(&mut cx, &mut plain(), i1, i2).unwrap();
        assert_eq!(cancelled, Some((cx.id(h).unwrap(), cx.id(g).unwrap())));

        let secret = deterministic_wide(w, 0x1234_5678 ^ u64::from(bits));
        let target = eval(&mut cx, e1, &[("h", secret)]);
        let got = solve_eq(&mut cx, &mut plain(), i1, &target).unwrap();
        assert_eq!(got, Some(Solved::Eq(cx.id(h).unwrap(), secret)));
    }

    // 2. Permutation polynomials (`2 * x * x + x` and `(x << 1) * x + x`) at 256 and 512 bits.
    for bits in [256u16, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        for poly_src in ["2 * x * x + x", "2 * (x * x) + x", "(x << 1) * x + x + 7"] {
            let mut cx = Context::new();
            let x = cx.parse("x", &o).unwrap();
            let y = cx.parse("y", &o).unwrap();
            let e = cx.parse(poly_src, &o).unwrap();
            let ey = cx.substitute(&[e], &[(x, y)]).unwrap()[0];

            assert_eq!(
                cx.prove(Query::Bijective { e, of: x }).unwrap(),
                Truth::True,
                "{poly_src} @ {bits}"
            );

            let (ie, iey) = (cx.id(e).unwrap(), cx.id(ey).unwrap());
            let (mut ca, mut cb) = (ie, iey);
            while let Some((p, q)) = cancel_layer(&mut cx, &mut plain(), ca, cb).unwrap() {
                (ca, cb) = (p, q);
            }
            assert_eq!((ca, cb), (cx.id(x).unwrap(), cx.id(y).unwrap()));

            let secret = deterministic_wide(w, 0xfeed_cafe ^ u64::from(bits));
            let target = eval(&mut cx, e, &[("x", secret)]);
            assert_eq!(
                solve_eq(&mut cx, &mut plain(), ie, &target).unwrap(),
                Some(Solved::Eq(cx.id(x).unwrap(), secret))
            );
        }

        // Injective widening (`zext` over a 256-bit permutation polynomial into 512 bits)
        // both recovers valid preimages and refutes out-of-range targets.
        if bits == 256 {
            let mut cx = Context::new();
            let x = cx.parse("x", &o).unwrap();
            let poly = cx.parse("2 * x * x + x", &o).unwrap();
            let wide = cx.zext(poly, Width::W512).unwrap();
            assert_eq!(
                cx.prove(Query::Injective { e: wide, of: x }).unwrap(),
                Truth::True
            );
            assert_eq!(
                cx.prove(Query::Bijective { e: wide, of: x }).unwrap(),
                Truth::False
            );
            let secret = deterministic_wide(Width::W256, 0x7777);
            let valid_target = eval(&mut cx, wide, &[("x", secret)]);
            let wi = cx.id(wide).unwrap();
            assert_eq!(
                solve_eq(&mut cx, &mut plain(), wi, &valid_target).unwrap(),
                Some(Solved::Eq(cx.id(x).unwrap(), secret))
            );
            let invalid_target = BitVec::smin(Width::W512);
            assert_eq!(
                solve_eq(&mut cx, &mut plain(), wi, &invalid_target).unwrap(),
                Some(Solved::Const(false))
            );
        }
    }

    // 3. Parametric T-functions `u - (((u << 1) | b) & h)` and block-triangular maps at 256 & 512 bits.
    for bits in [256u16, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        let mut cx = Context::new();
        let u = cx.parse("u", &o).unwrap();
        let v = cx.parse("v", &o).unwrap();
        let tf = cx.parse("u - (((u << 1) | b) & h)", &o).unwrap();
        let tf_v = cx.parse("v - (((v << 1) | b) & h)", &o).unwrap();

        assert_eq!(
            cx.prove(Query::Bijective { e: tf, of: u }).unwrap(),
            Truth::True,
            "T-function @ {bits}"
        );
        let (tf_id, tf_v_id) = (cx.id(tf).unwrap(), cx.id(tf_v).unwrap());
        assert_eq!(
            cancel_layer(&mut cx, &mut plain(), tf_id, tf_v_id).unwrap(),
            Some((cx.id(u).unwrap(), cx.id(v).unwrap()))
        );

        let b_const = cx.constant(&deterministic_wide(w, 0xaaaa_1111)).unwrap();
        let h_const = cx.constant(&deterministic_wide(w, 0xbbbb_2222)).unwrap();
        let b_sym = cx.parse("b", &o).unwrap();
        let h_sym = cx.parse("h", &o).unwrap();
        let tf_const = cx
            .substitute(&[tf], &[(b_sym, b_const), (h_sym, h_const)])
            .unwrap()[0];
        let secret = deterministic_wide(w, 0xcccc_3333 ^ u64::from(bits));
        let target = eval(&mut cx, tf_const, &[("u", secret)]);
        let tf_const_id = cx.id(tf_const).unwrap();
        assert_eq!(
            solve_eq(&mut cx, &mut plain(), tf_const_id, &target).unwrap(),
            Some(Solved::Eq(cx.id(u).unwrap(), secret))
        );

        // Block-triangular map splitting at `half = bits / 2`: low half is an odd-affine + xorshift
        // bijection, high half subtracts shifted low bits and adds low-half carry.
        let half = bits / 2;
        let low_mask = {
            let mut m = BitVec::ones(w);
            let sh = BitVec::wrapping_from_u64(w, u64::from(half));
            m = BitVec::un_unchecked(UnOp::Not, &BitVec::bin_unchecked(BinOp::Shl, &m, &sh));
            m
        };
        let mask_e = cx.constant(&low_mask).unwrap();
        let k_param = cx.symbol("k_p", w).unwrap();
        let h_param = cx.symbol("h_p", w).unwrap();
        let x = cx.symbol("x_blk", w).unwrap();
        let sh_half = cx.constant_u64(w, u64::from(half)).unwrap();
        let sh_near = cx.constant_u64(w, u64::from(half - 8)).unwrap();
        let three = cx.constant_u64(w, 3).unwrap();

        let x_mul = cx.bin(BinOp::Mul, x, three).unwrap();
        let x_add = cx.bin(BinOp::Add, x_mul, k_param).unwrap();
        let lo_part = cx.bin(BinOp::And, x_add, mask_e).unwrap();
        let carry = cx.cmp(CmpOp::Ult, lo_part, k_param).unwrap();
        let carry_w = cx.zext(carry, w).unwrap();

        let x_hi = cx.bin(BinOp::LShr, x, sh_half).unwrap();
        let x_near = cx.bin(BinOp::LShr, x, sh_near).unwrap();
        let masked_near = cx.bin(BinOp::And, x_near, h_param).unwrap();
        let hi_step = cx.bin(BinOp::Sub, x_hi, masked_near).unwrap();
        let hi_with_carry = cx.bin(BinOp::Add, hi_step, carry_w).unwrap();
        let hi_shifted = cx.bin(BinOp::Shl, hi_with_carry, sh_half).unwrap();
        let blk = cx.bin(BinOp::Or, hi_shifted, lo_part).unwrap();

        assert_eq!(
            cx.prove(Query::Bijective { e: blk, of: x }).unwrap(),
            Truth::True,
            "block-triangular @ {bits}"
        );

        let kc = cx.constant(&deterministic_wide(w, 0x5151)).unwrap();
        let hc = cx.constant(&deterministic_wide(w, 0x6262)).unwrap();
        let blk_const = cx
            .substitute(&[blk], &[(k_param, kc), (h_param, hc)])
            .unwrap()[0];
        let secret_x = deterministic_wide(w, 0x9999_8888 ^ u64::from(bits));
        let blk_target = eval(&mut cx, blk_const, &[("x_blk", secret_x)]);
        let blk_const_id = cx.id(blk_const).unwrap();
        assert_eq!(
            solve_eq(&mut cx, &mut plain(), blk_const_id, &blk_target).unwrap(),
            Some(Solved::Eq(cx.id(x).unwrap(), secret_x))
        );
    }
}

#[test]
fn hensel_refutes_nonlinear_opaque_predicates_up_to_512_bits() {
    use super::hensel::{HenselLimits, HenselOutcome, solve};
    use crate::ParseOptions;

    let limits = HenselLimits::default();
    for bits in [64u16, 128, 256, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);

        for src in [
            "(x * (x + 1)) & 1 == 1",
            "x * x + x + 1 == 0",
            "(x * (x | 1)) ^ ((x << 1) + 2) == 3",
            // Survives mod 2, mod 4, and mod 8; obstructed at bit 3 (mod 16).
            "(x * (x | 1)) ^ ((x << 1) + 6) == 1",
            // Wrapped in outer non-causal bijections.
            "bswap(x * x + x + 1) == 0",
            "rotl(x * x + 4 * y, 13) == rotl(3, 13)",
        ] {
            let mut cx = Context::new();
            let p = cx.parse(src, &o).unwrap();
            assert_eq!(
                solve(&cx, &[p], &limits).unwrap(),
                HenselOutcome::Unsat,
                "{src} @ {bits}"
            );
        }

        // Coupled 2-variable T-function systems obstructed at mod 4 and mod 8.
        for (p1_src, p2_src) in [
            ("(x * x + 2 * y) == 5", "(y * y + 2 * x) == 5"),
            ("(x * x + 2 * y) == 7", "(y * y + 4 * x) == 1"),
        ] {
            let mut cx = Context::new();
            let p1 = cx.parse(p1_src, &o).unwrap();
            let p2 = cx.parse(p2_src, &o).unwrap();
            assert_eq!(
                solve(&cx, &[p1, p2], &limits).unwrap(),
                HenselOutcome::Unsat,
                "{p1_src} && {p2_src} @ {bits}"
            );
        }
    }
}

#[test]
fn hensel_solves_and_enumerates_roots_with_known_bits_and_side_filters() {
    use super::hensel::{HenselLimits, HenselOutcome, enumerate, solve};
    use crate::ParseOptions;

    let limits = HenselLimits::default();

    // 1. Satisfiable nonlinear T-functions across 64, 128, 256, and 512 bits.
    for bits in [64u16, 128, 256, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        let mut cx = Context::new();
        let _x = cx.parse("x", &o).unwrap();
        let lhs = cx.parse("x * (x ^ 0x55) + (x << 3)", &o).unwrap();

        let secret = deterministic_wide(w, 0x4242_1337 ^ u64::from(bits));
        let target = eval(&mut cx, lhs, &[("x", secret)]);
        let tc = cx.constant(&target).unwrap();
        let pred = cx.eq(lhs, tc).unwrap();

        match solve(&cx, &[pred], &limits).unwrap() {
            HenselOutcome::Sat(model) => {
                assert_eq!(
                    cx.eval(&[pred], &model[..]).unwrap(),
                    [BitVec::from_bool(true)]
                );
            }
            other => panic!("expected Sat at {bits} bits, got {other:?}"),
        }

        // Coupled 2-variable Hensel system with invertible Jacobian mod 2 -> unique root!
        let mut cx2 = Context::new();
        let _x2 = cx2.parse("x", &o).unwrap();
        let _y2 = cx2.parse("y", &o).unwrap();
        let f1 = cx2.parse("x + 2 * y * y", &o).unwrap();
        let f2 = cx2.parse("y + 2 * x * x + (x << 2)", &o).unwrap();
        let sx = deterministic_wide(w, 0x1111_2222 ^ u64::from(bits));
        let sy = deterministic_wide(w, 0x3333_4444 ^ u64::from(bits));
        let c1 = eval(&mut cx2, f1, &[("x", sx), ("y", sy)]);
        let c2 = eval(&mut cx2, f2, &[("x", sx), ("y", sy)]);
        let c1e = cx2.constant(&c1).unwrap();
        let c2e = cx2.constant(&c2).unwrap();
        let eq1 = cx2.eq(f1, c1e).unwrap();
        let eq2 = cx2.eq(f2, c2e).unwrap();

        match solve(&cx2, &[eq1, eq2], &limits).unwrap() {
            HenselOutcome::Sat(model) => {
                assert_eq!(
                    model,
                    vec![(SymbolKey::from("x"), sx), (SymbolKey::from("y"), sy)]
                );
            }
            other => panic!("coupled system @ {bits}: {other:?}"),
        }
    }

    // 2. Multi-root modular quadratic `x * x == 25`: 4 roots mod 2^W (`5, -5, 2^(W-1)-5, 2^(W-1)+5`).
    for bits in [64u16, 128, 256, 512] {
        let w = Width::new(bits).unwrap();
        let o = ParseOptions::width(w);
        let mut cx = Context::new();
        let x = cx.parse("x", &o).unwrap();
        let eq = cx.parse("x * x == 25", &o).unwrap();

        let five = BitVec::wrapping_from_u64(w, 5);
        let neg_five = BitVec::un_unchecked(UnOp::Neg, &five);
        let half = BitVec::smin(w);
        let r3 = BitVec::bin_unchecked(BinOp::Sub, &half, &five);
        let r4 = BitVec::bin_unchecked(BinOp::Add, &half, &five);
        let mut expected = vec![five, neg_five, r3, r4];
        expected.sort();

        let got = enumerate(&cx, &[eq], x, 4, &limits).unwrap();
        assert_eq!(got, Some(expected.clone()), "quadratic roots @ {bits}");
        // Asking with limit = 3 must return None since 4 > 3 distinct roots exist.
        assert_eq!(enumerate(&cx, &[eq], x, 3, &limits).unwrap(), None);

        // End-of-lift non-causal filter `x <u 1000` selects `x == 5` uniquely.
        let small = cx.parse("x <u 1000", &o).unwrap();
        assert_eq!(
            solve(&cx, &[eq, small], &limits).unwrap(),
            HenselOutcome::Sat(vec![(SymbolKey::from("x"), five)])
        );
        assert_eq!(
            enumerate(&cx, &[eq, small], x, 4, &limits).unwrap(),
            Some(vec![five])
        );

        // End-of-lift non-causal filter `x >u 10` && `x <u 100` eliminates all 4 roots -> Unsat!
        let gt10 = cx.parse("x >u 10", &o).unwrap();
        let lt100 = cx.parse("x <u 100", &o).unwrap();
        assert_eq!(
            solve(&cx, &[eq, gt10, lt100], &limits).unwrap(),
            HenselOutcome::Unsat
        );
        assert_eq!(
            enumerate(&cx, &[eq, gt10, lt100], x, 4, &limits).unwrap(),
            Some(Vec::new())
        );

        // `declared_known`: pinning MSB = 1 and bit 1 = 1 selects the unique matching root or Unsat.
        let mut cx_kb = Context::new();
        let xk = cx_kb.parse("x", &o).unwrap();
        let eqk = cx_kb.parse("x * x == 25", &o).unwrap();
        // Force MSB = 0 and bit 1 = 0: among `{5 (..0101), 2^(W-1)-5 (..1011)}`, only `5` has MSB=0 and bit1=0.
        let zero_mask = BitVec::bin_unchecked(
            BinOp::Or,
            &BitVec::smin(w),
            &BitVec::wrapping_from_u64(w, 2),
        );
        let kb = KnownBits::new(zero_mask, BitVec::zero(w)).unwrap();
        cx_kb.declare_known(xk, kb).unwrap();
        assert_eq!(
            enumerate(&cx_kb, &[eqk], xk, 4, &limits).unwrap(),
            Some(vec![five])
        );

        // Force bit 0 = 0 on `x * x == 25` -> immediate Unsat at bit 0!
        let even_kb = KnownBits::new(BitVec::one(w), BitVec::zero(w)).unwrap();
        cx_kb.declare_known(xk, even_kb).unwrap();
        assert_eq!(
            solve(&cx_kb, &[eqk], &limits).unwrap(),
            HenselOutcome::Unsat
        );
    }
}

/// Random causal T-function builder over `syms` at width `w` (for differential fuzzing).
fn random_causal_expr(rng: &mut Rng, cx: &mut Context, syms: &[Expr], w: u16, depth: u32) -> Expr {
    let wd = width(w);
    let mask = if w >= 64 { u64::MAX } else { (1u64 << w) - 1 };
    if depth == 0 || rng.chance(1, 4) {
        let idx = rng.below((syms.len() + 2) as u64) as usize;
        if idx < syms.len() {
            return syms[idx];
        }
        return cx.constant_u64(wd, rng.next() & mask).unwrap();
    }
    let d = depth - 1;
    match rng.below(13) {
        0 => {
            let a = random_causal_expr(rng, cx, syms, w, d);
            let op = if rng.chance(1, 2) {
                UnOp::Not
            } else {
                UnOp::Neg
            };
            cx.un(op, a).unwrap()
        }
        1..=6 => {
            let op = [
                BinOp::Add,
                BinOp::Sub,
                BinOp::Mul,
                BinOp::And,
                BinOp::Or,
                BinOp::Xor,
            ][rng.below(6) as usize];
            let a = random_causal_expr(rng, cx, syms, w, d);
            let b = random_causal_expr(rng, cx, syms, w, d);
            cx.bin(op, a, b).unwrap()
        }
        7 => {
            let a = random_causal_expr(rng, cx, syms, w, d);
            let s = cx.constant_u64(wd, rng.below(u64::from(w) + 1)).unwrap();
            cx.bin(BinOp::Shl, a, s).unwrap()
        }
        8 if w > 1 => {
            // Narrow causal expression extended via zext or sext.
            let nw = 1 + rng.below(u64::from(w - 1)) as u16;
            let a = random_causal_expr(rng, cx, syms, w, d);
            let trunc = cx.extract(a, 0, width(nw)).unwrap();
            if rng.chance(1, 2) {
                cx.zext(trunc, wd).unwrap()
            } else {
                cx.sext(trunc, wd).unwrap()
            }
        }
        9 if w > 1 => {
            // Concat of two narrower causal truncations.
            let lw = 1 + rng.below(u64::from(w - 1)) as u16;
            let hw = w - lw;
            let a = random_causal_expr(rng, cx, syms, w, d);
            let b = random_causal_expr(rng, cx, syms, w, d);
            let hi = cx.extract(a, 0, width(hw)).unwrap();
            let lo = cx.extract(b, 0, width(lw)).unwrap();
            cx.concat(hi, lo).unwrap()
        }
        10 => {
            // Select with a bit-0 causal condition.
            let src = random_causal_expr(rng, cx, syms, w, d);
            let cond = cx.extract(src, 0, Width::W1).unwrap();
            let t = random_causal_expr(rng, cx, syms, w, d);
            let e = random_causal_expr(rng, cx, syms, w, d);
            cx.select(cond, t, e).unwrap()
        }
        _ => {
            let a = random_causal_expr(rng, cx, syms, w, d);
            let k = cx.constant_u64(wd, rng.next() & mask).unwrap();
            cx.bin(BinOp::Add, a, k).unwrap()
        }
    }
}

#[test]
fn hensel_differential_soundness_against_truth_tables() {
    use super::hensel::{HenselLimits, HenselOutcome, enumerate, solve};

    let mut rng = Rng(0x2ad1_c001);
    let limits = HenselLimits::default();
    let (mut sat_cnt, mut unsat_cnt, mut enum_cnt) = (0u32, 0u32, 0u32);

    for case in 0..800 {
        let two_vars = case % 3 == 0;
        let w: u16 = if two_vars || case % 2 == 0 { 4 } else { 6 };
        let wd = width(w);
        let mask = (1u64 << w) - 1;
        let mut cx = Context::new();
        let x = cx.symbol("x", wd).unwrap();
        let syms = if two_vars {
            let y = cx.symbol("y", wd).unwrap();
            vec![x, y]
        } else {
            vec![x]
        };

        // Optionally declare 1 known bit on `x`.
        let x_kb = if rng.chance(1, 3) {
            let bit = rng.below(u64::from(w));
            let m = BitVec::wrapping_from_u64(wd, 1u64 << bit);
            let kb = if rng.chance(1, 2) {
                KnownBits::new(m, BitVec::zero(wd)).unwrap()
            } else {
                KnownBits::new(BitVec::zero(wd), m).unwrap()
            };
            cx.declare_known(x, kb).unwrap();
            Some(kb)
        } else {
            None
        };

        let mut preds = Vec::new();
        let lhs1 = random_causal_expr(&mut rng, &mut cx, &syms, w, 3);
        let rhs1 = if rng.chance(2, 3) {
            cx.constant_u64(wd, rng.next() & mask).unwrap()
        } else {
            random_causal_expr(&mut rng, &mut cx, &syms, w, 2)
        };
        preds.push(cx.eq(lhs1, rhs1).unwrap());

        if rng.chance(1, 2) {
            let lhs2 = random_causal_expr(&mut rng, &mut cx, &syms, w, 2);
            let rhs2 = cx.constant_u64(wd, rng.next() & mask).unwrap();
            preds.push(cx.eq(lhs2, rhs2).unwrap());
        }

        // Occasionally add a non-causal side filter (`Ult`, `Slt`, or `Ne`).
        if rng.chance(1, 3) {
            let bound = cx.constant_u64(wd, rng.next() & mask).unwrap();
            let op = [CmpOp::Ult, CmpOp::Ule, CmpOp::Slt, CmpOp::Ne][rng.below(4) as usize];
            preds.push(cx.cmp(op, x, bound).unwrap());
        }

        let target = random_causal_expr(&mut rng, &mut cx, &syms, w, 2);

        // Exhaustive truth table over all valid assignments (`2^4 = 16`, `2^6 = 64`, or `2^8 = 256`).
        let mut valid_models = Vec::new();
        let mut target_vals = Vec::new();
        let y_limit = if two_vars { 1u64 << w } else { 1 };
        for xv in 0..(1u64 << w) {
            let xbv = val(w, xv);
            if x_kb.is_some_and(|kb| !kb.contains(&xbv)) {
                continue;
            }
            for yv in 0..y_limit {
                let env: Vec<(SymbolKey, BitVec)> = if two_vars {
                    vec![
                        (SymbolKey::from("x"), xbv),
                        (SymbolKey::from("y"), val(w, yv)),
                    ]
                } else {
                    vec![(SymbolKey::from("x"), xbv)]
                };
                let evals = cx.eval(&preds, &env[..]).unwrap();
                if evals.iter().all(|v| v.bit(0) == Some(true)) {
                    valid_models.push(env.clone());
                    target_vals.push(cx.eval(&[target], &env[..]).unwrap()[0]);
                }
            }
        }
        target_vals.sort();
        target_vals.dedup();

        match solve(&cx, &preds, &limits).unwrap() {
            HenselOutcome::Sat(model) => {
                sat_cnt += 1;
                assert!(
                    !valid_models.is_empty(),
                    "Hensel returned Sat on an unsatisfiable system: {model:?}"
                );
                if let Some(kb) = x_kb
                    && let Some(&(_, xv)) = model.iter().find(|(k, _)| *k == SymbolKey::from("x"))
                {
                    assert!(kb.contains(&xv), "model violated declared_known");
                }
                let check = cx.eval(&preds, &model[..]).unwrap();
                assert!(
                    check.iter().all(|v| v.bit(0) == Some(true)),
                    "model failed predicate evaluation"
                );
            }
            HenselOutcome::Unsat => {
                unsat_cnt += 1;
                assert!(
                    valid_models.is_empty(),
                    "SOUNDNESS BUG: Hensel returned Unsat when valid models exist: {:?}",
                    valid_models[0]
                );
            }
            HenselOutcome::Unknown => {}
        }

        if let Some(got_vals) = enumerate(&cx, &preds, target, 16, &limits).unwrap() {
            enum_cnt += 1;
            assert!(got_vals.len() <= 16);
            assert_eq!(got_vals, target_vals, "enumerate mismatch on case {case}");
        }
    }

    assert!(sat_cnt > 100, "too few Sat cases: {sat_cnt}");
    assert!(unsat_cnt > 200, "too few Unsat cases: {unsat_cnt}");
    assert!(enum_cnt > 300, "too few enumerated cases: {enum_cnt}");
}
