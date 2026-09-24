//! MBA module tests: the expression type, lowering and lifting, the signature solver, caches;
//! the batched evaluator and the certificates in their own modules.

mod batch;
mod certify;
mod nf;
pub(crate) mod random;

use super::*;
use crate::testutil::{Gen, Rng};
use crate::{BinOp, BitVec, Context, ParseOptions, Width};

#[test]
fn mba_expr_checks_widths_and_evaluates() {
    let w = Width::W8;
    let mut m = MbaExpr::new(vec![w, w]);
    let x = m.push(MOp::Var(0), &[]).unwrap();
    let y = m.push(MOp::Var(1), &[]).unwrap();
    let a = m.push(MOp::And, &[x, y]).unwrap();
    let two = m
        .push(MOp::Const(BitVec::from_u64(w, 2).unwrap()), &[])
        .unwrap();
    let t = m.push(MOp::Mul, &[a, two]).unwrap();
    let xo = m.push(MOp::Xor, &[x, y]).unwrap();
    let _ = m.push(MOp::Add, &[xo, t]).unwrap();
    let v = |a: u64, b: u64| {
        vec![
            BitVec::from_u64(w, a).unwrap(),
            BitVec::from_u64(w, b).unwrap(),
        ]
    };
    for (a, b) in [(3, 5), (200, 100), (255, 255)] {
        assert_eq!(m.eval(&v(a, b)).unwrap().to_u64(), Some((a + b) & 0xff));
    }
    assert!(m.is_linear());
    let s = m.shape();
    assert!(s.mixed);
    assert_eq!((s.vars, s.degree), (2, 1));
    // Width errors.
    let z = m.push(MOp::Const(BitVec::zero(Width::W16)), &[]).unwrap();
    assert_eq!(m.push(MOp::Add, &[x, z]), Err(MbaError::Width));
    assert_eq!(m.push(MOp::Shl(8), &[x]), Err(MbaError::Width));
    assert_eq!(m.push(MOp::Var(9), &[]), Err(MbaError::UnknownVar));
    assert_eq!(m.push_cast(MOp::Zext, x, Width::W8), Err(MbaError::Width));
    assert_eq!(m.push(MOp::Add, &[x, 99]), Err(MbaError::BadOperand));
    // Keys are content hashes.
    let mut m2 = MbaExpr::new(vec![w, w]);
    let x2 = m2.push(MOp::Var(0), &[]).unwrap();
    let y2 = m2.push(MOp::Var(1), &[]).unwrap();
    m2.push(MOp::And, &[x2, y2]).unwrap();
    let mut m3 = m2.clone();
    assert_eq!(m2.key(), m3.key());
    m3.push(MOp::Not, &[2]).unwrap();
    assert_ne!(m2.key(), m3.key());
    // A product of two variables is not linear.
    let mut p = MbaExpr::new(vec![w, w]);
    let (a, b) = (
        p.push(MOp::Var(0), &[]).unwrap(),
        p.push(MOp::Var(1), &[]).unwrap(),
    );
    p.push(MOp::Mul, &[a, b]).unwrap();
    assert!(!p.is_linear());
    assert_eq!(p.shape().degree, 2);
}

#[test]
fn lowering_and_lifting_round_trip() {
    let mut g = Gen {
        rng: Rng(0x10e7),
        max_w: 8,
        vars: Vec::new(),
    };
    let lim = MbaLimits {
        max_vars: 64,
        max_nodes: 4096,
        ..MbaLimits::default()
    };
    let mut lowered = 0;
    for _ in 0..500 {
        let mut cx = Context::new();
        let w = 1 + g.rng.below(8) as u16;
        let (e, _) = g.expr(&mut cx, w, 4);
        let Ok((m, b)) = lower(&cx, e, &lim) else {
            continue;
        };
        lowered += 1;
        let back = lift(&mut cx, &m, &b).unwrap();
        assert_eq!(b.len(), m.vars().len());
        if back == e {
            continue;
        }
        // A concat is lowered as a shift and an addition: the same value, another node.
        let concat = {
            let mut stack = vec![cx.id(e).unwrap()];
            let mut found = false;
            while let Some(i) = stack.pop() {
                found |= cx.node(i).op == crate::expr::OpCode::Concat;
                stack.extend(cx.node(i).children());
            }
            found
        };
        assert!(concat, "{}", cx.display(e));
        let (m2, _) = lower(&cx, back, &lim).unwrap();
        let bits: u32 = m.vars().iter().map(|w| u32::from(w.bits())).sum();
        if bits <= 16 && m2.vars() == m.vars() {
            assert!(random::equal_everywhere(&m, &m2), "{}", cx.display(e));
        }
    }
    assert!(lowered > 100, "{lowered}");
}

#[test]
fn signature_solver_is_correct_and_complete_on_linear_mba() {
    let mut rng = Rng(0x5157);
    let solver = SignatureSolver;
    let mut simplified = 0;
    for i in 0..400 {
        let w = Width::new([4, 8, 16, 64, 128][i % 5]).unwrap();
        let t = 1 + rng.below(3) as u32;
        let mut m = MbaExpr::new(vec![w; t as usize]);
        let vars: Vec<u32> = (0..t).map(|k| m.push(MOp::Var(k), &[]).unwrap()).collect();
        // A random combination of random bitwise functions.
        let mut acc = m
            .push(MOp::Const(BitVec::wrapping_from_u64(w, rng.next())), &[])
            .unwrap();
        for _ in 0..(1 + rng.below(4)) {
            let mut f = vars[rng.below(u64::from(t)) as usize];
            for _ in 0..rng.below(3) {
                let o = vars[rng.below(u64::from(t)) as usize];
                let op = [MOp::And, MOp::Or, MOp::Xor][rng.below(3) as usize];
                f = m.push(op, &[f, o]).unwrap();
                if rng.chance(1, 3) {
                    f = m.push(MOp::Not, &[f]).unwrap();
                }
            }
            let k = m
                .push(MOp::Const(BitVec::wrapping_from_u64(w, rng.next())), &[])
                .unwrap();
            let term = m.push(MOp::Mul, &[f, k]).unwrap();
            acc = m.push(MOp::Add, &[acc, term]).unwrap();
        }
        let _ = acc;
        match solver.solve(&m, &MbaBudget::default()) {
            MbaAnswer::Simplified { expr, .. } => {
                simplified += 1;
                for _ in 0..64 {
                    let v: Vec<BitVec> = (0..t)
                        .map(|_| BitVec::wrapping_from_limbs(w, &[rng.next(), rng.next()]))
                        .collect();
                    assert_eq!(m.eval(&v), expr.eval(&v));
                }
            }
            MbaAnswer::NoSimpler => {}
            other => panic!("{other:?}"),
        }
    }
    assert!(simplified > 100, "{simplified}");
    // Non-linear inputs are unsupported.
    let w = Width::W8;
    let mut p = MbaExpr::new(vec![w, w]);
    let (a, b) = (
        p.push(MOp::Var(0), &[]).unwrap(),
        p.push(MOp::Var(1), &[]).unwrap(),
    );
    p.push(MOp::Mul, &[a, b]).unwrap();
    assert!(matches!(
        solver.solve(&p, &MbaBudget::default()),
        MbaAnswer::Unsupported(_)
    ));
}

#[test]
fn memory_cache_is_bounded() {
    let c = MemoryCache::new(2);
    for k in 0..5u64 {
        c.put(&CacheKey([k, k]), &CacheEntry::NoSimpler);
    }
    assert_eq!(c.len(), 2);
    assert!(c.get(&CacheKey([0, 0])).is_none());
    assert_eq!(c.get(&CacheKey([4, 4])), Some(CacheEntry::NoSimpler));
    let _ = (Context::new(), ParseOptions::default(), BinOp::Add);
}

#[test]
fn not_of_a_constant_is_uniform_only_when_the_constant_is() {
    // `x & ~0xf0` is not a linear MBA: `~0xf0` is a constant but not 0 or all-ones, so the
    // corner signature does not determine it (it agrees with `x·0xf1` at both corners).
    let w = Width::W8;
    let masked = |k: u64, op: MOp| {
        let mut m = MbaExpr::new(vec![w]);
        let x = m.push(MOp::Var(0), &[]).unwrap();
        let c = m
            .push(MOp::Const(BitVec::from_u64(w, k).unwrap()), &[])
            .unwrap();
        let nc = m.push(MOp::Not, &[c]).unwrap();
        m.push(op, &[x, nc]).unwrap();
        m
    };
    assert!(!masked(0xf0, MOp::And).is_linear());
    assert!(!masked(0x0f, MOp::Or).is_linear());
    assert!(!masked(0x01, MOp::Xor).is_linear());
    // Uniform constants stay uniform through `~`, and `~c` is still a fine coefficient.
    assert!(masked(0x00, MOp::And).is_linear());
    assert!(masked(0xff, MOp::Or).is_linear());
    assert!(masked(0xf0, MOp::Mul).is_linear());
    // The solver never answers wrongly on them.
    for k in [0u64, 1, 0x0f, 0xf0, 0xff] {
        for op in [MOp::And, MOp::Or, MOp::Xor] {
            let m = masked(k, op);
            if let MbaAnswer::Simplified { expr, .. } =
                SignatureSolver.solve(&m, &MbaBudget::default())
            {
                for x in 0..256 {
                    let v = [BitVec::from_u64(w, x).unwrap()];
                    assert_eq!(m.eval(&v), expr.eval(&v), "k={k:#x} {op:?} x={x}");
                }
            }
        }
    }
}
