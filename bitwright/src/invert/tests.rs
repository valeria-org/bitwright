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
