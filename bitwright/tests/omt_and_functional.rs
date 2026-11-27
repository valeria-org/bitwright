#![cfg(all(feature = "prove", feature = "smtlib"))]

use std::collections::HashSet;

use bitwright::engine::{Clock, Deadline};
use bitwright::prove::Unknown;
use bitwright::smtlib::run;
use bitwright::solve::{Config, Optimum, Solver, Status};
use bitwright::{
    BinOp, BitVec, CmpOpExt, Context, KnownBits, ParseOptions, SymbolId, Truth, Width,
};

struct ExpiredClock;

impl Clock for ExpiredClock {
    fn now_ticks(&self) -> u64 {
        100
    }
}

#[test]
fn omt_unsigned_and_signed_across_widths() {
    // 1-bit: unsigned [0, 1], signed [-1 (0b1), 0 (0b0)].
    {
        let mut cx = Context::new();
        let x = cx.symbol("x", Width::W1).unwrap();
        let mut s = Solver::default();
        assert_eq!(
            s.minimize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::zero(Width::W1))
        );
        assert_eq!(s.value(&mut cx, x).unwrap(), Some(BitVec::zero(Width::W1)));
        assert_eq!(
            s.maximize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::one(Width::W1))
        );
        assert_eq!(s.value(&mut cx, x).unwrap(), Some(BitVec::one(Width::W1)));
        assert_eq!(
            s.minimize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::one(Width::W1))
        );
        assert_eq!(s.value(&mut cx, x).unwrap(), Some(BitVec::one(Width::W1)));
        assert_eq!(
            s.maximize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::zero(Width::W1))
        );
        assert_eq!(s.value(&mut cx, x).unwrap(), Some(BitVec::zero(Width::W1)));
    }

    // 8-bit: wrapped interval `(x <u 10) | (x >u 245)` with odd-value requirement.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &o).unwrap();
        let wrapped = cx
            .parse("((x <u 10) | (x >u 245)) & ((x & 1) == 1)", &o)
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, wrapped).unwrap();

        // Unsigned: min = 1 (0x01), max = 255 (0xff).
        assert_eq!(
            s.minimize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u64(Width::W8, 1).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(1));
        assert_eq!(
            s.maximize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u64(Width::W8, 255).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(255));

        // Signed: 247 is -9 (0xf7), 9 is +9 (0x09).
        assert_eq!(
            s.minimize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(Width::W8, -9).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_i128(), Some(-9));
        assert_eq!(
            s.maximize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(Width::W8, 9).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_i128(), Some(9));
    }

    // 32-bit: nonlinear `x <u 0x10000 & x * x <u 50` and optimal witness retrieval on coupled `y`.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let c1 = cx
            .parse("(x <u 0x10000) & ((x * x) <u 50) & ((x * x) >=u 9)", &o)
            .unwrap();
        let c2 = cx.parse("y == x * 10 + 3", &o).unwrap();
        let mut s = Solver::default();
        s.assert(&cx, c1).unwrap();
        s.assert(&cx, c2).unwrap();

        assert_eq!(
            s.minimize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u64(Width::W32, 3).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(3));
        assert_eq!(s.value(&mut cx, y).unwrap().unwrap().to_u64(), Some(33));

        assert_eq!(
            s.maximize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u64(Width::W32, 7).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u64(), Some(7));
        assert_eq!(s.value(&mut cx, y).unwrap().unwrap().to_u64(), Some(73));
    }

    // 64-bit: signed range straddling zero with linear modular congruence.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let x = cx.parse("x", &o).unwrap();
        let c = cx
            .parse("(x >=s -1000) & (x <=s 2500) & ((x & 7) == 5)", &o)
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, c).unwrap();

        // Smallest `x >= -1000` with `x & 7 == 5`: -1000 == -125 * 8 (rem 0), so -1000 + 5 = -995.
        assert_eq!(
            s.minimize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(Width::W64, -995).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_i128(), Some(-995));

        // Largest `x <= 2500` with `x & 7 == 5`: 2500 = 312 * 8 + 4, so 2496 + 5 = 2501 > 2500 -> 2493.
        assert_eq!(
            s.maximize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(Width::W64, 2493).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_i128(), Some(2493));
    }

    // 128-bit: wide unsigned and signed bounds above 2^96.
    {
        let mut cx = Context::new();
        let w = Width::W128;
        let x = cx.symbol("x", w).unwrap();
        let lo_u = (1u128 << 100) + 19;
        let hi_u = (1u128 << 100) + 991;
        let lo_e = cx.constant_u128(w, lo_u).unwrap();
        let hi_e = cx.constant_u128(w, hi_u).unwrap();
        let c_lo = cx.cmp(CmpOpExt::Uge, x, lo_e).unwrap();
        let c_hi = cx.cmp(CmpOpExt::Ule, x, hi_e).unwrap();

        let mut s = Solver::default();
        s.assert(&cx, c_lo).unwrap();
        s.assert(&cx, c_hi).unwrap();
        assert_eq!(
            s.minimize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u128(w, lo_u).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u128(), Some(lo_u));
        assert_eq!(
            s.maximize(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_u128(w, hi_u).unwrap())
        );
        assert_eq!(s.value(&mut cx, x).unwrap().unwrap().to_u128(), Some(hi_u));

        // Signed 128-bit bounds in `[-((1 << 90) + 77), (1 << 90) + 55]`.
        let mut s_signed = Solver::default();
        let slo = -((1i128 << 90) + 77);
        let shi = (1i128 << 90) + 55;
        let slo_e = cx.constant_i128(w, slo).unwrap();
        let shi_e = cx.constant_i128(w, shi).unwrap();
        let g1 = cx.cmp(CmpOpExt::Sge, x, slo_e).unwrap();
        let g2 = cx.cmp(CmpOpExt::Sle, x, shi_e).unwrap();
        s_signed.assert(&cx, g1).unwrap();
        s_signed.assert(&cx, g2).unwrap();
        assert_eq!(
            s_signed.minimize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(w, slo).unwrap())
        );
        assert_eq!(
            s_signed.maximize_signed(&mut cx, x).unwrap(),
            Optimum::Found(BitVec::from_i128(w, shi).unwrap())
        );
    }

    // Unsat, constant objective, and expired deadline.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &o).unwrap();
        let k = cx.constant_u64(Width::W8, 42).unwrap();
        let mut s = Solver::default();
        assert_eq!(
            s.minimize(&mut cx, k).unwrap(),
            Optimum::Found(BitVec::from_u64(Width::W8, 42).unwrap())
        );

        let clock = ExpiredClock;
        let expired = Deadline::new(&clock, 50);
        let non_const = cx.parse("x >u 3", &o).unwrap();
        s.assert(&cx, non_const).unwrap();
        assert_eq!(
            s.minimize_within(&mut cx, x, &[], Some(expired)).unwrap(),
            Optimum::Unknown(Unknown::Deadline)
        );

        let contradiction = cx.parse("x <u 2", &o).unwrap();
        assert_eq!(
            s.minimize_within(&mut cx, x, &[contradiction], None)
                .unwrap(),
            Optimum::Unsat
        );
    }
}

#[test]
fn tighten_facts_recovers_ranges_and_known_bits_beyond_abstract_transfer() {
    // 1. Coupled algebraic + masked expression where `cx.facts(y)` is `Facts::top`.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let y = cx.parse("y", &o).unwrap();
        assert_eq!(cx.facts(y).unwrap(), bitwright::Facts::top(Width::W32));

        // `(x ^ k) + 2 * (x & k) - (x + k)` is identically 0, so `y == 0x50 | ((z & 3) << 2)`:
        // exact values are `{0x50, 0x54, 0x58, 0x5c}`:
        // - umin = 0x50, umax = 0x5c
        // - smin = 0x50, smax = 0x5c
        // - bits 0, 1, 5, and 7..32 are provably 0; bits 4 and 6 (0x50 = 0b0101_0000) are provably 1!
        let c = cx
            .parse(
                "y == ((x ^ k) + 2 * (x & k) - (x + k)) + (0x50 | ((z & 3) << 2))",
                &o,
            )
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, c).unwrap();

        let tf = s.tighten_facts(&mut cx, y).unwrap().unwrap();
        assert_eq!(tf.urange().lo().to_u64(), Some(0x50));
        assert_eq!(tf.urange().hi().to_u64(), Some(0x5c));
        assert_eq!(tf.srange().lo().to_i128(), Some(0x50));
        assert_eq!(tf.srange().hi().to_i128(), Some(0x5c));
        assert_eq!(tf.known().known_zero().bit(0), Some(true));
        assert_eq!(tf.known().known_zero().bit(1), Some(true));
        assert_eq!(tf.known().known_one().bit(4), Some(true));
        assert_eq!(tf.known().known_one().bit(6), Some(true));
        // Bits 2 and 3 can take both 0 and 1 across `z & 3` in `0..=3`.
        assert_eq!(tf.known().known().bit(2), Some(false));
        assert_eq!(tf.known().known().bit(3), Some(false));
    }

    // 2. Wrapped signed interval on bare symbol `x` (`-5 <=s x <=s 7` on W8):
    // unsigned spans `[0, 255]` (`0x00` and `0xff = -1` are both feasible), while signed is `[-5, 7]`.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &o).unwrap();
        let c = cx.parse("(x >=s -5) & (x <=s 7)", &o).unwrap();
        let mut s = Solver::default();
        s.assert(&cx, c).unwrap();

        let tf = s.tighten_facts(&mut cx, x).unwrap().unwrap();
        assert_eq!(tf.urange().lo().to_u64(), Some(0));
        assert_eq!(tf.urange().hi().to_u64(), Some(255));
        assert_eq!(tf.srange().lo().to_i128(), Some(-5));
        assert_eq!(tf.srange().hi().to_i128(), Some(7));

        let unsat_a = cx.parse("x >s 10", &o).unwrap();
        assert!(
            s.tighten_facts_within(&mut cx, x, &[unsat_a], None)
                .unwrap()
                .is_none()
        );
    }
}

fn assert_valid_functional_def(
    s: &mut Solver,
    cx: &mut Context,
    target: Expr,
    inputs: &[bitwright::Expr],
    assumptions: &[bitwright::Expr],
) -> bitwright::Expr {
    use bitwright::Expr;
    let target: Expr = target;
    let cand = s
        .functional_def_within(cx, target, inputs, assumptions, None)
        .unwrap()
        .expect("expected closed-form functional definition");
    assert_eq!(cx.width(cand).unwrap(), cx.width(target).unwrap());
    let allowed: HashSet<SymbolId> = cx.symbols_in(inputs).unwrap().into_iter().collect();
    for sym in cx.symbols_in(&[cand]).unwrap() {
        assert!(
            allowed.contains(&sym),
            "synthesized candidate {} references non-input symbol {:?}",
            cx.display(cand),
            cx.symbol_key(sym)
        );
    }
    let ne = cx.cmp(CmpOpExt::Ne, target, cand).unwrap();
    let mut check_a = assumptions.to_vec();
    check_a.push(ne);
    assert_eq!(s.check_assuming(cx, &check_a).unwrap(), Status::Unsat);
    cand
}

use bitwright::Expr;

#[test]
fn is_determined_by_and_declared_known_semantics() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::W8);
    let x = cx.parse("x", &o).unwrap();
    let y = cx.parse("y", &o).unwrap();
    let z = cx.parse("z", &o).unwrap();
    let c = cx.symbol("c", Width::W1).unwrap();

    // `x * 2 == y`: `y` is determined by `x`, whereas `x` is NOT determined by `y` (MSB of `x` is lost).
    let mut s = Solver::default();
    let eq = cx.parse("x * 2 == y", &o).unwrap();
    s.assert(&cx, eq).unwrap();
    assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::True);
    assert_eq!(s.is_determined_by(&mut cx, x, &[y]).unwrap(), Truth::False);
    assert!(s.functional_def(&mut cx, x, &[y]).unwrap().is_none());

    // Declaring MSB of `x` known-zero (`x < 128`) makes `x * 2 == y` injective, so `x` IS determined by `y`!
    let msb_zero = KnownBits::new(
        BitVec::from_u64(Width::W8, 0x80).unwrap(),
        BitVec::zero(Width::W8),
    )
    .unwrap();
    cx.declare_known(x, msb_zero).unwrap();
    assert_eq!(s.is_determined_by(&mut cx, x, &[y]).unwrap(), Truth::True);
    let x_def = assert_valid_functional_def(&mut s, &mut cx, x, &[y], &[]);
    // Verify at `y = 42` (`x = 21`):
    let y42 = cx.parse("y == 42", &o).unwrap();
    assert_eq!(s.check_assuming(&mut cx, &[y42]).unwrap(), Status::Sat);
    assert_eq!(s.value(&mut cx, x_def).unwrap().unwrap().to_u64(), Some(21));

    // Scoped assumption turns conditional `y == select(c, z + 1, k)` into a function of `[z]`.
    let mut s2 = Solver::default();
    let z1 = cx.parse("z + 1", &o).unwrap();
    let k = cx.parse("k", &o).unwrap();
    let chosen = cx.select(c, z1, k).unwrap();
    let branch_eq = cx.cmp(CmpOpExt::Eq, y, chosen).unwrap();
    s2.assert(&cx, branch_eq).unwrap();
    assert_eq!(s2.is_determined_by(&mut cx, y, &[z]).unwrap(), Truth::False);
    assert_eq!(
        s2.is_determined_by_within(&mut cx, y, &[z], &[c], None)
            .unwrap(),
        Truth::True
    );
    let _ = assert_valid_functional_def(&mut s2, &mut cx, y, &[z], &[c]);
}

#[test]
fn functional_def_recovers_linear_modular_coupled_gf2_and_nonlinear_witnesses() {
    // 1. Implicit modular-inverse: `y * 0x9e3779b1 == x + 5` (32-bit) and 128-bit odd multiplier.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W32);
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let eq = cx.parse("y * 0x9e3779b1 == x + 5", &o).unwrap();
        let mut s = Solver::default();
        s.assert(&cx, eq).unwrap();
        assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::True);
        let _ = assert_valid_functional_def(&mut s, &mut cx, y, &[x], &[]);

        // 128-bit modular-affine inverse where `y` appears twice (`3 * y == y + 2 * y == x + 9`),
        // exercising Tier B's mod-2^128 interpolation!
        let mut cx128 = Context::new();
        let xw = cx128.symbol("x", Width::W128).unwrap();
        let yw = cx128.symbol("y", Width::W128).unwrap();
        let two = cx128.constant_u128(Width::W128, 2).unwrap();
        let nine = cx128.constant_u128(Width::W128, 9).unwrap();
        let two_y = cx128.bin(BinOp::Mul, two, yw).unwrap();
        let lhs = cx128.bin(BinOp::Add, yw, two_y).unwrap();
        let rhs = cx128.bin(BinOp::Add, xw, nine).unwrap();
        let eq128 = cx128.cmp(CmpOpExt::Eq, lhs, rhs).unwrap();
        let mut s128 = Solver::default();
        s128.assert(&cx128, eq128).unwrap();
        let _ = assert_valid_functional_def(&mut s128, &mut cx128, yw, &[xw], &[]);
    }

    // 2. Coupled multi-assertion elimination (`t == x ^ k`, `y + t == (x & k) * 2 + (x ^ k)`).
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W64);
        let x = cx.parse("x", &o).unwrap();
        let k = cx.parse("k", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let eq1 = cx.parse("t == (x ^ k)", &o).unwrap();
        let eq2 = cx.parse("y + t == (x & k) * 2 + (x ^ k)", &o).unwrap();
        let mut s = Solver::default();
        s.assert(&cx, eq1).unwrap();
        s.assert(&cx, eq2).unwrap();

        let cand = assert_valid_functional_def(&mut s, &mut cx, y, &[x, k], &[]);
        // Verify algebraically against `(x & k) * 2`.
        let expected = cx.parse("(x & k) * 2", &o).unwrap();
        let mut check_s = Solver::default();
        let diff = cx.cmp(CmpOpExt::Ne, cand, expected).unwrap();
        check_s.assert(&cx, diff).unwrap();
        assert_eq!(check_s.check(&mut cx).unwrap(), Status::Unsat);
    }

    // 3. Implicit 3-tap GF(2)-affine bijection: `y ^ rotl(y, 1) ^ rotl(y, 3) == x ^ 0xa5` on W8.
    // Because weight 3 is odd on W8 (2^3), `I + R_1 + R_3` is invertible over GF(2), even though
    // `y` occurs 3 times and cannot be isolated by single-occurrence peeling!
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        let eq = cx
            .parse("(y ^ rotl(y, 1) ^ rotl(y, 3)) == (x ^ 0xa5)", &o)
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, eq).unwrap();
        assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::True);
        let _ = assert_valid_functional_def(&mut s, &mut cx, y, &[x], &[]);
    }

    // 4. Nonlinear implicit piecewise & bitwise witnesses synthesized via observational CEGIS.
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W8);
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        // Relational piecewise specification without a direct `y == ...` equation:
        // when `x <u 10`, `y == x + 3`; when `x >=u 10`, `y == x * 2`.
        let lo_branch = cx.parse("~(x <u 10) | (y == x + 3)", &o).unwrap();
        let hi_branch = cx.parse("(x <u 10) | (y == x * 2)", &o).unwrap();
        let mut s = Solver::default();
        s.assert(&cx, lo_branch).unwrap();
        s.assert(&cx, hi_branch).unwrap();
        assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::True);
        let _ = assert_valid_functional_def(&mut s, &mut cx, y, &[x], &[]);
    }

    // 5. Finite small-domain nonlinear map (`x <u 5`) and edge cases (`[]` inputs, `Unsat`).
    {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::W16);
        let x = cx.parse("x", &o).unwrap();
        let y = cx.parse("y", &o).unwrap();
        // Implicit integer square root on `x <u 4`: `y <u 3 & y * y <=u x & (y + 1) * (y + 1) >u x`.
        let spec = cx
            .parse(
                "(x <u 4) & (y <u 3) & ((y * y) <=u x) & (((y + 1) * (y + 1)) >u x)",
                &o,
            )
            .unwrap();
        let mut s = Solver::default();
        s.assert(&cx, spec).unwrap();
        assert_eq!(s.is_determined_by(&mut cx, y, &[x]).unwrap(), Truth::True);
        let _ = assert_valid_functional_def(&mut s, &mut cx, y, &[x], &[]);

        // Empty `inputs` returns `Some(const)` only when `target` is constant, else `None`.
        assert!(s.functional_def(&mut cx, y, &[]).unwrap().is_none());
        let zero_id = cx
            .parse("z == (x ^ y) + 2 * (x & y) - (x + y) + 77", &o)
            .unwrap();
        let z = cx.parse("z", &o).unwrap();
        s.assert(&cx, zero_id).unwrap();
        let z_const = assert_valid_functional_def(&mut s, &mut cx, z, &[], &[]);
        assert_eq!(
            cx.as_const(z_const).unwrap(),
            Some(BitVec::from_u64(Width::W16, 77).unwrap())
        );

        // Unsatisfiable assumptions -> `None`.
        let bad = cx.parse("x == 99", &o).unwrap();
        assert!(
            s.functional_def_within(&mut cx, y, &[x], &[bad], None)
                .unwrap()
                .is_none()
        );
    }
}

#[test]
fn smtlib_omt_end_to_end() {
    let cfg = Config::default();
    let script = "
        (set-logic QF_BV)
        (declare-const x (_ BitVec 16))
        (declare-const y (_ BitVec 16))
        (assert (bvult x #x0100))
        (assert (bvult (bvmul x x) #x0032))
        (assert (= y (bvadd x #x0010)))
        (maximize x)
        (minimize y)
        (check-sat)
        (get-objectives)
        (get-value (x y))
    ";
    let mut out = String::new();
    let summary = run(&mut Context::new(), script, &cfg, &mut out).unwrap();
    assert_eq!((summary.sat, summary.unsat, summary.errors), (1, 0, 0));
    let expected = "\
sat
(objectives
 (x #x0007)
 (y #x0017)
)
((x #x0007) (y #x0017))
";
    assert_eq!(out, expected);
}

#[test]
fn solver_uses_2adic_hensel_for_wide_nonlinear_t_functions() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(256).unwrap());
    // 256-bit quadratic opaque predicate: x * (x + 1) is always even, so == 2 * y + 1 is Unsat!
    let mut s = Solver::new(Config::default().with_quick(None).with_probes(0));
    let unsat_pred = cx.parse("x * (x + 1) == (y << 1) + 1", &o).unwrap();
    s.assert(&cx, unsat_pred).unwrap();
    assert_eq!(s.check(&mut cx).unwrap(), Status::Unsat);
    assert_eq!(s.decided_by(), Some(bitwright::solve::DecidedBy::Hensel));
    assert_eq!(s.tier(), Some(bitwright::solve::Tier::Search));

    // 256-bit non-linear T-function root recovery and multi-root enumeration.
    let mut s2 = Solver::new(Config::default().with_quick(None).with_probes(0));
    let eq = cx
        .parse(
            "x * (x ^ 0x55) + (x << 3) == (0x123456789abcdef:256 * (0x123456789abcdef:256 ^ 0x55)) + (0x123456789abcdef:256 << 3)",
            &o,
        )
        .unwrap();
    s2.assert(&cx, eq).unwrap();
    assert_eq!(s2.check(&mut cx).unwrap(), Status::Sat);
    assert_eq!(s2.decided_by(), Some(bitwright::solve::DecidedBy::Hensel));
    let x = cx.parse("x", &o).unwrap();
    let vx = s2.value(&mut cx, x).unwrap().unwrap();
    let check = cx
        .eval(&[eq], &[(bitwright::SymbolKey::from("x"), vx)][..])
        .unwrap();
    assert_eq!(check[0].to_u64(), Some(1));

    // Quadratic `z * z == 17` mod 2^64 has exactly 4 distinct 2-adic roots!
    let o64 = ParseOptions::width(Width::W64);
    let mut s3 = Solver::default();
    let q = cx.parse("z * z == 17", &o64).unwrap();
    let z = cx.parse("z", &o64).unwrap();
    s3.assert(&cx, q).unwrap();
    let bitwright::solve::Values::Exact(roots) = s3.enumerate_values(&mut cx, z, 8).unwrap() else {
        panic!("expected exact 4 roots");
    };
    assert_eq!(roots.len(), 4);
    for r in &roots {
        assert_eq!(r.to_u64().unwrap().wrapping_mul(r.to_u64().unwrap()), 17);
    }
}
