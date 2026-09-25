//! Floating point on arbitrary byte-encoded DAGs, in tiny and standard formats: no panic; the
//! built expression (construction's identities included) evaluates like the independent
//! reference semantics (`bitwright-ref::fp`) applied operation by operation; its facts contain
//! every value; the simplifier's result (standard, and deobfuscation with the MBA service)
//! equals it; and it survives SMT-LIB export and import. At points derived from the input,
//! special values (zeros, infinities, NaNs with and without a payload, subnormals, the extremes)
//! included.
#![no_main]

use std::rc::Rc;

use bitwright::engine::{Budget, Engine, Run, Strategy};
use bitwright::fp::{FpCmpOp, FpFormat, FpOp, FpTest, RoundingMode};
use bitwright::mba::MbaConfig;
use bitwright::{BinOp, BitVec, Context, Expr, FnEnv, SymbolKey, Width, smtlib};
use bitwright_ref::Bits;
use bitwright_ref::fp as reference;
use libfuzzer_sys::fuzz_target;

#[allow(dead_code)] // the byte reader only
mod common;
use common::Bytes;

/// The formats: every tiny shape the reference reaches exhaustively, and the standard ones.
const FORMATS: [(u32, u32); 10] = [
    (2, 3),
    (3, 3),
    (3, 4),
    (4, 3),
    (5, 11),
    (8, 8),
    (8, 24),
    (11, 53),
    (15, 64),
    (15, 113),
];

/// A node of the reference's view of the DAG, evaluated operation by operation.
enum R {
    Sym(usize),
    Const(BitVec),
    Fp(FpOp, FpFormat, Vec<Rc<R>>),
    Neg(FpFormat, Rc<R>),
    Abs(FpFormat, Rc<R>),
    CopySign(FpFormat, Rc<R>, Rc<R>),
    Cmp(FpFormat, FpCmpOp, Rc<R>, Rc<R>),
    Test(FpFormat, FpTest, Rc<R>),
    Select(Rc<R>, Rc<R>, Rc<R>),
}

fn fmt(f: FpFormat) -> reference::Format {
    reference::Format {
        eb: f.eb() as u16,
        sb: f.sb() as u16,
    }
}

fn rm(r: RoundingMode) -> reference::Rm {
    match r {
        RoundingMode::Rne => reference::Rm::Rne,
        RoundingMode::Rna => reference::Rm::Rna,
        RoundingMode::Rtp => reference::Rm::Rtp,
        RoundingMode::Rtn => reference::Rm::Rtn,
        _ => reference::Rm::Rtz,
    }
}

fn bits(v: &BitVec) -> Bits {
    Bits::from_limbs(v.width().bits(), v.limbs())
}

fn value(b: &Bits) -> BitVec {
    BitVec::wrapping_from_limbs(Width::new(b.width()).unwrap(), &b.to_limbs())
}

fn truth(b: bool) -> Bits {
    Bits::from_u128(1, u128::from(b))
}

impl R {
    fn eval(&self, env: &[Bits]) -> Bits {
        match self {
            R::Sym(i) => env[*i].clone(),
            R::Const(v) => bits(v),
            R::Neg(f, a) => reference::neg(fmt(*f), &a.eval(env)),
            R::Abs(f, a) => reference::abs(fmt(*f), &a.eval(env)),
            R::CopySign(f, a, b) => reference::copysign(fmt(*f), &a.eval(env), &b.eval(env)),
            R::Cmp(f, op, a, b) => {
                let (x, y) = (a.eval(env), b.eval(env));
                let f = fmt(*f);
                truth(match op {
                    FpCmpOp::Eq => reference::eq(f, &x, &y),
                    FpCmpOp::Lt => reference::lt(f, &x, &y),
                    FpCmpOp::Le => reference::le(f, &x, &y),
                    FpCmpOp::Gt => reference::lt(f, &y, &x),
                    _ => reference::le(f, &y, &x),
                })
            }
            R::Test(f, t, a) => {
                let (f, x) = (fmt(*f), a.eval(env));
                truth(match t {
                    FpTest::Nan => reference::is_nan(f, &x),
                    FpTest::Infinite => reference::is_infinite(f, &x),
                    FpTest::Zero => reference::is_zero(f, &x),
                    FpTest::Subnormal => reference::is_subnormal(f, &x),
                    FpTest::Normal => reference::is_normal(f, &x),
                    FpTest::Negative => reference::is_negative(f, &x),
                    _ => reference::is_positive(f, &x),
                })
            }
            R::Select(c, t, e) => {
                if c.eval(env).bit(0) {
                    t.eval(env)
                } else {
                    e.eval(env)
                }
            }
            R::Fp(op, f, args) => {
                let a: Vec<Bits> = args.iter().map(|x| x.eval(env)).collect();
                let f = fmt(*f);
                match *op {
                    FpOp::Add(r) => reference::add(f, rm(r), &a[0], &a[1]),
                    FpOp::Mul(r) => reference::mul(f, rm(r), &a[0], &a[1]),
                    FpOp::Div(r) => reference::div(f, rm(r), &a[0], &a[1]),
                    FpOp::Fma(r) => reference::fma(f, rm(r), &a[0], &a[1], &a[2]),
                    FpOp::Sqrt(r) => reference::sqrt(f, rm(r), &a[0]),
                    FpOp::Rem => reference::rem(f, &a[0], &a[1]),
                    FpOp::RoundToIntegral(r) => reference::round_to_integral(f, rm(r), &a[0]),
                    FpOp::Min => reference::min(f, &a[0], &a[1]),
                    FpOp::Max => reference::max(f, &a[0], &a[1]),
                    FpOp::Eq => truth(reference::eq(f, &a[0], &a[1])),
                    FpOp::Lt => truth(reference::lt(f, &a[0], &a[1])),
                    FpOp::Le => truth(reference::le(f, &a[0], &a[1])),
                    FpOp::Convert { to, rm: r } => reference::to_fp(f, fmt(to), rm(r), &a[0]),
                    FpOp::FromSInt(r) => reference::from_sint(f, rm(r), &a[0]),
                    FpOp::FromUInt(r) => reference::from_uint(f, rm(r), &a[0]),
                    FpOp::ToSInt(r, w) => reference::to_sint(f, rm(r), &a[0], w.bits()),
                    FpOp::ToUInt(r, w) => reference::to_uint(f, rm(r), &a[0], w.bits()),
                    _ => unreachable!("an operation this target does not build"),
                }
            }
        }
    }
}

fn bin(op: BinOp, a: &BitVec, b: &BitVec) -> BitVec {
    BitVec::apply_bin(op, a, b).unwrap()
}

/// A float of format `f`: a special value, or bits from `h`; negative half the time.
fn special(f: FpFormat, h: u64, k: u64) -> BitVec {
    let w = f.width();
    let one = BitVec::one(w);
    let shl = |s: u32| {
        bin(BinOp::Shl, &one, &BitVec::wrapping_from_u64(w, u64::from(s)))
    };
    let min_normal = shl(f.sb() - 1);
    let picks = [
        f.zero(false),
        f.inf(false),
        f.nan(),
        // A NaN with a payload.
        bin(BinOp::Or, &f.nan(), &one),
        one,
        bin(BinOp::Sub, &min_normal, &one),
        min_normal,
        bin(BinOp::Sub, &f.inf(false), &one),
        f.from_uint(RoundingMode::Rne, &BitVec::one(Width::W8)),
        f.from_uint(RoundingMode::Rne, &BitVec::wrapping_from_u64(Width::W8, h & 0xff)),
        BitVec::wrapping_from_limbs(w, &[h, h.rotate_left(23)]),
        BitVec::wrapping_from_limbs(w, &[h, !h]),
    ];
    let v = picks[(k % picks.len() as u64) as usize];
    if (h >> 3) & 1 == 1 {
        f.neg(&v).unwrap()
    } else {
        v
    }
}

fuzz_target!(|data: &[u8]| {
    let mut b = Bytes(data);
    let (eb, sb) = FORMATS[usize::from(b.byte()) % FORMATS.len()];
    let f = FpFormat::new(eb, sb).unwrap();
    let w = f.width();
    let mut cx = Context::new();
    let names = ["a", "b", "c"];
    let syms: Vec<Expr> = names.iter().map(|n| cx.symbol(*n, w).unwrap()).collect();
    let pick_rm = |b: &mut Bytes<'_>| RoundingMode::ALL[usize::from(b.byte()) % 5];
    let mut stack: Vec<(Expr, Rc<R>)> = Vec::new();
    for _ in 0..24 {
        if b.0.is_empty() {
            break;
        }
        let op = b.byte();
        let pop = |stack: &mut Vec<(Expr, Rc<R>)>, i: usize| {
            stack
                .pop()
                .unwrap_or_else(|| (syms[i % 3], Rc::new(R::Sym(i % 3))))
        };
        let e: (Expr, Rc<R>) = match op % 14 {
            0 | 1 => {
                let i = usize::from(b.byte()) % 3;
                (syms[i], Rc::new(R::Sym(i)))
            }
            2 => {
                let v = special(f, b.u64(), u64::from(b.byte()));
                (cx.constant(&v).unwrap(), Rc::new(R::Const(v)))
            }
            3 | 4 => {
                let r = pick_rm(&mut b);
                let fop = [
                    FpOp::Add(r),
                    FpOp::Mul(r),
                    FpOp::Div(r),
                    FpOp::Rem,
                    FpOp::Min,
                    FpOp::Max,
                ][usize::from(b.byte()) % 6];
                let (y, x) = (pop(&mut stack, 1), pop(&mut stack, 0));
                let e = cx.fp(fop, f, &[x.0, y.0]).unwrap();
                (e, Rc::new(R::Fp(fop, f, vec![x.1, y.1])))
            }
            5 => {
                // Subtraction as the builder writes it: a + neg(b).
                let r = pick_rm(&mut b);
                let (y, x) = (pop(&mut stack, 1), pop(&mut stack, 0));
                let e = cx.fp_sub(f, r, x.0, y.0).unwrap();
                let ny = Rc::new(R::Neg(f, y.1));
                (e, Rc::new(R::Fp(FpOp::Add(r), f, vec![x.1, ny])))
            }
            6 => {
                let r = pick_rm(&mut b);
                let (z, y, x) = (pop(&mut stack, 2), pop(&mut stack, 1), pop(&mut stack, 0));
                let e = cx.fp(FpOp::Fma(r), f, &[x.0, y.0, z.0]).unwrap();
                (e, Rc::new(R::Fp(FpOp::Fma(r), f, vec![x.1, y.1, z.1])))
            }
            7 => {
                let r = pick_rm(&mut b);
                let fop = if b.byte() % 2 == 0 {
                    FpOp::Sqrt(r)
                } else {
                    FpOp::RoundToIntegral(r)
                };
                let x = pop(&mut stack, 0);
                (
                    cx.fp(fop, f, &[x.0]).unwrap(),
                    Rc::new(R::Fp(fop, f, vec![x.1])),
                )
            }
            8 => {
                let x = pop(&mut stack, 0);
                match b.byte() % 3 {
                    0 => (cx.fp_neg(f, x.0).unwrap(), Rc::new(R::Neg(f, x.1))),
                    1 => (cx.fp_abs(f, x.0).unwrap(), Rc::new(R::Abs(f, x.1))),
                    _ => {
                        let y = pop(&mut stack, 1);
                        (
                            cx.fp_copysign(f, x.0, y.0).unwrap(),
                            Rc::new(R::CopySign(f, x.1, y.1)),
                        )
                    }
                }
            }
            9 | 10 => {
                // A condition on floats choosing between two floats.
                let c = if b.byte() % 2 == 0 {
                    let op = [FpCmpOp::Eq, FpCmpOp::Lt, FpCmpOp::Le, FpCmpOp::Gt, FpCmpOp::Ge]
                        [usize::from(b.byte()) % 5];
                    let (y, x) = (pop(&mut stack, 1), pop(&mut stack, 0));
                    (
                        cx.fp_cmp(f, op, x.0, y.0).unwrap(),
                        Rc::new(R::Cmp(f, op, x.1, y.1)),
                    )
                } else {
                    let t = [
                        FpTest::Nan,
                        FpTest::Infinite,
                        FpTest::Zero,
                        FpTest::Subnormal,
                        FpTest::Normal,
                        FpTest::Negative,
                        FpTest::Positive,
                    ][usize::from(b.byte()) % 7];
                    let x = pop(&mut stack, 0);
                    (cx.fp_test(f, t, x.0).unwrap(), Rc::new(R::Test(f, t, x.1)))
                };
                let (e, t) = (pop(&mut stack, 2), pop(&mut stack, 1));
                (
                    cx.select(c.0, t.0, e.0).unwrap(),
                    Rc::new(R::Select(c.1, t.1, e.1)),
                )
            }
            11 => {
                // Through an integer and back.
                let widths = [3u16, 8, 16, 32, 65];
                let iw = Width::new(widths[usize::from(b.byte()) % widths.len()]).unwrap();
                let (r1, r2) = (pick_rm(&mut b), pick_rm(&mut b));
                let signed = b.byte() % 2 == 0;
                let (to, from) = if signed {
                    (FpOp::ToSInt(r1, iw), FpOp::FromSInt(r2))
                } else {
                    (FpOp::ToUInt(r1, iw), FpOp::FromUInt(r2))
                };
                let x = pop(&mut stack, 0);
                let i = cx.fp(to, f, &[x.0]).unwrap();
                let ri = Rc::new(R::Fp(to, f, vec![x.1]));
                (
                    cx.fp(from, f, &[i]).unwrap(),
                    Rc::new(R::Fp(from, f, vec![ri])),
                )
            }
            12 => {
                // Through another format and back.
                let (eb2, sb2) = FORMATS[usize::from(b.byte()) % FORMATS.len()];
                let g = FpFormat::new(eb2, sb2).unwrap();
                let (r1, r2) = (pick_rm(&mut b), pick_rm(&mut b));
                let x = pop(&mut stack, 0);
                let there = FpOp::Convert { to: g, rm: r1 };
                let back = FpOp::Convert { to: f, rm: r2 };
                let y = cx.fp(there, f, &[x.0]).unwrap();
                let ry = Rc::new(R::Fp(there, f, vec![x.1]));
                (
                    cx.fp(back, g, &[y]).unwrap(),
                    Rc::new(R::Fp(back, g, vec![ry])),
                )
            }
            _ => match stack.last() {
                Some((e, r)) => (*e, r.clone()),
                None => continue,
            },
        };
        stack.push(e);
    }
    let Some((root, rroot)) = stack.pop() else {
        return;
    };
    assert_eq!(cx.width(root).unwrap(), w);
    let budget = Budget::default()
        .with_node_visits(1 << 16)
        .with_pass_work(1 << 18);
    let standard = Engine::standard();
    let deob = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .unwrap();
    let simplified: Vec<Expr> = [&standard, &deob]
        .iter()
        .map(|eng| {
            eng.run(&mut cx, &[root], Run::default().with_per_call(budget))
                .unwrap()
                .roots[0]
                .expr
        })
        .collect();
    let facts = cx.facts(root).unwrap();
    let text = smtlib::export(&mut cx, &[root]).expect("export");
    let mut other = Context::new();
    let back = smtlib::import(&mut other, &text)
        .unwrap_or_else(|e| panic!("export does not read back: {e}\n{text}"));
    let back = back.definition("root0").unwrap();
    for k in 0..24u64 {
        let vals: Vec<BitVec> = (0..3u64)
            .map(|i| {
                let h = (k * 3 + i + 1).wrapping_mul(0x9e37_79b9_7f4a_7c15) ^ data.len() as u64;
                special(f, h, h >> 11)
            })
            .collect();
        let env = FnEnv(|key: &SymbolKey, _| {
            names
                .iter()
                .position(|n| SymbolKey::from(*n) == *key)
                .map(|i| vals[i])
        });
        let got = cx.eval(&[root], &env).unwrap()[0];
        let want = value(&rroot.eval(&vals.iter().map(bits).collect::<Vec<_>>()));
        assert_eq!(got, want, "{} disagrees with the reference", cx.display(root));
        assert!(facts.contains(&got), "{} = {got} not in {facts:?}", cx.display(root));
        for &s in &simplified {
            let z = cx.eval(&[s], &env).unwrap()[0];
            assert_eq!(z, got, "{} became {}", cx.display(root), cx.display(s));
        }
        let z = other.eval(&[back], &env).unwrap()[0];
        assert_eq!(z, got, "SMT-LIB round trip of {}:\n{text}", cx.display(root));
    }
});
