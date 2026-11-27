//! End-to-end simplification, invertibility, and soundness tests for:
//! 1. Functional polynomial canonicalization (`Z / 2^W Z` falling-factorial vanishing ideal)
//!    and value-level `2^k`-adic Hensel invariant folding across `1..=512` bits.
//! 2. 2-adic Euler-Fermat squaring & power-tower valuation algebra (`1..=512` bits).
//! 3. Affine-shift & odd-affine basis alignment across bitwise, MBA, and polynomial passes.
//! 4. Hamming-weight (`popcnt`) valuation linear algebra, `BLSR` pairing, parity homomorphism,
//!    and `bitrev` bit-scan dualities.
//! 5. BMI2 `pdep`/`pext` `GF(2)` linear algebra, inversion, and Morton bit-provenance round-trips.
//! 6. Guarded branch-invariant `select` elimination and wide (`65..=512`-bit) MBA cofactors.
#![cfg(all(feature = "mba", feature = "prove"))]

use bitwright::engine::{Engine, Run, Strategy};
use bitwright::mba::MbaConfig;
use bitwright::{
    Assumptions, BitVec, CmpOpExt, Context, Expr, ParseOptions, Query, SymbolKey, Truth, Width,
};

fn deobf_engine() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(MbaConfig::default()))
        .build()
        .unwrap()
}

fn assert_simplifies_to(src: &str, want: &str, w: u16) {
    let width = Width::new(w).unwrap();
    let opts = ParseOptions::width(width);
    let mut cx = Context::new();
    let e = cx.parse(src, &opts).unwrap();
    let expected = cx.parse(want, &opts).unwrap();
    let eng = deobf_engine();
    let out = eng.simplify(&mut cx, e).unwrap().expr;
    assert_eq!(
        out,
        expected,
        "width {w}: expected `{src}` -> `{}`, got `{}`",
        cx.display(expected),
        cx.display(out)
    );
    verify_sample_eq(&mut cx, e, out, width);
}

fn assert_sound_nonconstant(src: &str, w: u16) -> (Context, Expr, Expr) {
    let width = Width::new(w).unwrap();
    let opts = ParseOptions::width(width);
    let mut cx = Context::new();
    let e = cx.parse(src, &opts).unwrap();
    let eng = deobf_engine();
    let out = eng.simplify(&mut cx, e).unwrap().expr;
    verify_sample_eq(&mut cx, e, out, width);
    assert!(
        cx.as_const(out).unwrap().is_none(),
        "width {w}: `{src}` unsoundly folded to constant `{}`",
        cx.display(out)
    );
    (cx, e, out)
}

fn verify_sample_eq(cx: &mut Context, a: Expr, b: Expr, width: Width) {
    let samples: [u64; 10] = [
        0,
        1,
        2,
        3,
        5,
        7,
        0x5555_5555_5555_5555,
        0xaaaa_aaaa_aaaa_aaaa,
        0xdead_beef_cafe_babe,
        u64::MAX,
    ];
    let names = ["x", "y", "z", "w", "a", "b", "u"];
    for (idx, &sx) in samples.iter().enumerate() {
        let sy = samples[(idx + 3) % samples.len()];
        let sz = samples[(idx + 7) % samples.len()];
        let sw = samples[(idx + 5) % samples.len()];
        let mk = |v: u64, hi_salt: u64| -> BitVec {
            let mut limbs = [0u64; 8];
            limbs[0] = v;
            for (k, limb) in limbs.iter_mut().enumerate().skip(1) {
                *limb = v
                    .wrapping_mul(0x9e37_79b9_7f4a_7c15u64.wrapping_add(k as u64))
                    .wrapping_add(hi_salt);
            }
            BitVec::wrapping_from_limbs(width, &limbs)
        };
        let vals = [mk(sx, 1), mk(sy, 2), mk(sz, 3), mk(sw, 4)];
        let env: Vec<(SymbolKey, BitVec)> = names
            .iter()
            .enumerate()
            .map(|(i, &n)| (SymbolKey::from(n), vals[i % vals.len()]))
            .collect();
        let res = cx.eval(&[a, b], env.as_slice()).unwrap();
        assert_eq!(
            res[0],
            res[1],
            "evaluation mismatch at sample {idx} between `{}` and `{}`",
            cx.display(a),
            cx.display(b)
        );
    }
}

#[test]
fn vanishing_polynomials_and_hensel_value_invariants() {
    // 1. Falling-factorial vanishing ideal across `8, 32, 64, 128, 256, 512` bits:
    //    `v_2(2!) = 1 => 2^(W-1) * (x^2 + x) == 0 (mod 2^W)`,
    //    `v_2(4!) = 3 => 2^(W-3) * x*(x-1)*(x-2)*(x-3) == 0 (mod 2^W)`.
    for w in [8u16, 32, 64, 128, 256, 512] {
        let s1 = w - 1;
        let s3 = w - 3;
        assert_simplifies_to(&format!("((x * x + x) << {s1})"), "0", w);
        assert_simplifies_to(&format!("((x * x - x) << {s1}) + y"), "y", w);
        assert_simplifies_to(
            &format!("((x * (x - 1) * (x - 2) * (x - 3)) << {s3})"),
            "0",
            w,
        );
        assert_simplifies_to(
            &format!("((x * (x - 1) * (x - 2) * (x - 3)) << {s3}) + z"),
            "z",
            w,
        );
        // Multivariate vanishing product: `(x^2 - x) * (y^2 - y)` has valuation `>= 1 + 1 = 2`.
        let s2 = w - 2;
        assert_simplifies_to(
            &format!("(((x * x - x) * (y * y - y)) << {s2}) + z"),
            "z",
            w,
        );
    }

    // 2. Soundness: shifting by one bit too few (`W - 2` for degree 2, `W - 4` for degree 4)
    //    is NOT identically zero (`x = 1 => 2 != 0` or `x = 4 => 24 << (W - 4) != 0`).
    for w in [8u16, 64, 256] {
        let s_bad2 = w - 2;
        assert_sound_nonconstant(&format!("((x * (x + 1)) << {s_bad2})"), w);
        let s_bad4 = w - 4;
        assert_sound_nonconstant(
            &format!("((x * (x - 1) * (x - 2) * (x - 3)) << {s_bad4})"),
            w,
        );
    }

    // 3. Multi-variable value-level Hensel `2^k`-adic folding under demanded masks and even multiplies.
    assert_simplifies_to(
        "((x * x + x + y * y + y + z * z + z + w * w + w) & 1)",
        "0",
        64,
    );
    assert_simplifies_to("(((2 * x + 1) * (2 * x + 1)) & 7)", "1", 64);
    assert_simplifies_to("(((2 * x + 1) * (2 * x + 1) - 1) << 61)", "0", 64);
    // Even-constant multiply demanded-mask narrowing: `* 12` has `tz = 2`, so `& 63` only reads low 4 bits.
    assert_simplifies_to("(((x + 16) * 12) & 63)", "((x * 12) & 63)", 64);
}

#[test]
fn euler_fermat_squaring_and_power_towers() {
    // 1. Odd base `(x | 1)^(2^(W-2)) == 1 (mod 2^W)` and unknown-parity `x^(2^(W-2)) == x & 1 (mod 2^W)`.
    for w in [8u16, 16, 32, 64, 128, 256, 512] {
        let steps = (w - 2) as usize;
        let mut odd_chain = String::from("let s0 = x | 1; ");
        let mut any_chain = String::from("let s0 = x; ");
        for i in 1..=steps {
            let prev = i - 1;
            odd_chain.push_str(&format!("let s{i} = s{prev} * s{prev}; "));
            any_chain.push_str(&format!("let s{i} = s{prev} * s{prev}; "));
        }
        odd_chain.push_str(&format!("s{steps}"));
        any_chain.push_str(&format!("s{steps}"));
        assert_simplifies_to(&odd_chain, "1", w);
        assert_simplifies_to(&any_chain, "x & 1", w);
    }

    // 2. Demanded-mask prefix of shorter squaring chains: `x^16 = x^(2^4) == x & 1 (mod 64)`.
    for w in [16u16, 64, 256] {
        let src_ok =
            "let s1 = x * x; let s2 = s1 * s1; let s3 = s2 * s2; let s4 = s3 * s3; s4 & 63";
        assert_simplifies_to(src_ok, "x & 1", w);

        // Soundness: mod 128 (`& 127`) for `x^16` is NOT `x & 1` (at `x = 3`, `3^16 mod 128 = 65 != 1`)!
        let src_not_one = "let s1 = x * x; let s2 = s1 * s1; let s3 = s2 * s2; let s4 = s3 * s3; (s4 & 127) ^ (x & 1)";
        assert_sound_nonconstant(src_not_one, w);
    }
}

#[test]
fn affine_shift_and_odd_affine_basis_alignment() {
    // 1. Carry-free shifted slice polynomial cancellation across `32, 64, 128, 256`.
    for w in [32u16, 64, 128, 256] {
        let full =
            format!("let s = (x << 4) + 0x70; zext<{w}>(extract<4, 8>(s)) - ((x + 7) & 0xff)");
        assert_simplifies_to(&full, "0", w);
    }

    // 2. Shifted-translate & odd-affine MBA basis alignment:
    //    `s = (x << 4) + 0x70` -> `(s & 0xf0) + (s | 0xf0) - (x << 4)` folds to `0x70 + 0xf0 = 0x160`.
    assert_simplifies_to(
        "let s = (x << 4) + 0x70; (s & 0xf0) + (s | 0xf0) - (x << 4)",
        "0x160",
        64,
    );
    //    Odd-affine `u = x * 5 + 7`: `(u & 0xff) + (u & ~0xff) - x * 5 -> 7`.
    for w in [16u16, 64, 128] {
        assert_simplifies_to(
            "let u = x * 5 + 7; (u & 0xff) + (u & ~0xff) - x * 5",
            "7",
            w,
        );
    }
}

#[test]
fn popcnt_valuation_algebra_parity_and_bitscan_duals() {
    for w in [8u16, 32, 64, 128, 256, 512] {
        // Inclusion-exclusion: `popcnt(x) + popcnt(y) - popcnt(x | y) - popcnt(x & y) == 0`.
        assert_simplifies_to(
            "popcnt(x) + popcnt(y) - popcnt(x | y) - popcnt(x & y)",
            "0",
            w,
        );
        // Complement sum: `popcnt(x) + popcnt(~x) == W`.
        assert_simplifies_to("popcnt(x) + popcnt(~x)", &format!("{w}"), w);
        // XOR distance: `popcnt(x) + popcnt(y) - 2 * popcnt(x & y) == popcnt(x ^ y)`.
        assert_simplifies_to(
            "popcnt(x) + popcnt(y) - 2 * popcnt(x & y)",
            "popcnt(x ^ y)",
            w,
        );
        // Complementary constant-mask partition: `popcnt(x & M) + popcnt(x & ~M) == popcnt(x)`.
        assert_simplifies_to("popcnt(x & 0x55) + popcnt(x & ~0x55)", "popcnt(x)", w);
        // `BLSR` lowest-set-bit clear: `popcnt(x) - popcnt(x & (x - 1)) == zext(x != 0)`.
        assert_simplifies_to(
            "popcnt(x) - popcnt(x & (x - 1))",
            &format!("zext<{w}>(x != 0)"),
            w,
        );
        // Parity homomorphism: `(popcnt(x ^ y) ^ popcnt(x) ^ popcnt(y)) & 1 == 0`,
        // and `(popcnt(x) + popcnt(y)) & 1 == popcnt(x ^ y) & 1`.
        assert_simplifies_to("(popcnt(x ^ y) ^ popcnt(x) ^ popcnt(y)) & 1", "0", w);
        assert_simplifies_to(
            "((popcnt(x) + popcnt(y)) & 1) ^ (popcnt(x ^ y) & 1)",
            "0",
            w,
        );
        // Bit-scan dualities over `bitrev`.
        assert_simplifies_to("clz(bitrev(x))", "ctz(x)", w);
        assert_simplifies_to("ctz(bitrev(x))", "clz(x)", w);
    }

    // Soundness: `popcnt(x) + popcnt(y) - popcnt(x | y)` (missing `- popcnt(x & y)`) != 0!
    assert_sound_nonconstant("popcnt(x) + popcnt(y) - popcnt(x | y)", 64);
}

#[test]
fn bmi2_pdep_pext_gf2_and_bit_provenance_algebra() {
    // 1. Multi-atom `GF(2)` homomorphism over `pdep` and `pext` across `16, 64, 128, 256`.
    for w in [16u16, 64, 128, 256] {
        assert_simplifies_to(
            "pdep(x ^ y, 0x5555) ^ pdep(x, 0x5555)",
            "pdep(y, 0x5555)",
            w,
        );
        assert_simplifies_to(
            "pext(x ^ y, 0x5555) ^ pext(x, 0x5555)",
            "pext(y, 0x5555)",
            w,
        );
        // Morton / Z-order round-trip: `pext(pdep(x, M) | pdep(y, ~M), M) == x & low_mask(popcnt(M))`.
        assert_simplifies_to(
            "pext(pdep(x, 0x5555) | pdep(y, ~0x5555), 0x5555)",
            "x & 0xff",
            w,
        );
        // Full bit-partition reconstruction: `pdep(pext(x, M), M) | pdep(pext(x, ~M), ~M) == x`.
        assert_simplifies_to(
            "pdep(pext(x, 0x5555), 0x5555) | pdep(pext(x, ~0x5555), ~0x5555)",
            "x",
            w,
        );
        // Hamming weight of `pext`: `popcnt(pext(x, M)) == popcnt(x & M)`.
        assert_simplifies_to("popcnt(pext(x, 0x5555)) - popcnt(x & 0x5555)", "0", w);
    }

    // 2. Bijective 64-bit Morton interleave `(pdep(x, 0x5555_5555_5555_5555) | pdep(x >>u 32, 0xaaaa_aaaa_aaaa_aaaa))`
    //    is proved bijective in `GF(2)` and solved against constants by `Engine`!
    let mut cx = Context::new();
    let opts = ParseOptions::width(Width::W64);
    let morton = cx
        .parse(
            "pdep(x, 0x5555555555555555) | pdep(x >>u 32, 0xaaaaaaaaaaaaaaaa)",
            &opts,
        )
        .unwrap();
    let sym_x = cx.parse("x", &opts).unwrap();
    assert_eq!(
        cx.prove(Query::Bijective {
            e: morton,
            of: sym_x
        })
        .unwrap(),
        Truth::True
    );
    let target = BitVec::from_u64(Width::W64, 0xdead_beef_cafe_babe).unwrap();
    let target_c = cx.constant(&target).unwrap();
    let eq_morton = cx.cmp(CmpOpExt::Eq, morton, target_c).unwrap();
    let solved = Engine::standard()
        .simplify(&mut cx, eq_morton)
        .unwrap()
        .expr;
    let mut assump_morton = Assumptions::new();
    assump_morton.assume_true(&mut cx, solved).unwrap();
    let recovered_x = Engine::standard()
        .run(
            &mut cx,
            &[sym_x],
            Run::default().with_assumptions(&assump_morton),
        )
        .unwrap()
        .roots[0]
        .expr;
    let pre = cx
        .as_const(recovered_x)
        .unwrap()
        .expect("Morton equation solved to constant preimage");
    let check = cx
        .eval(&[morton], [(SymbolKey::from("x"), pre)].as_slice())
        .unwrap()[0];
    assert_eq!(check, target);

    // Also test assumption propagation on injective partial `pdep(x, 0x5555) == pdep(0xa5, 0x5555)`.
    let eq_pred = cx
        .parse("pdep(x, 0x5555) == pdep(0xa5, 0x5555)", &opts)
        .unwrap();
    let low_byte = cx.parse("x & 0xff", &opts).unwrap();
    let mut assump = Assumptions::new();
    assump.assume_true(&mut cx, eq_pred).unwrap();
    let out = Engine::standard()
        .run(
            &mut cx,
            &[low_byte],
            Run::default().with_assumptions(&assump),
        )
        .unwrap();
    assert_eq!(out.roots[0].expr, cx.parse("0xa5", &opts).unwrap());

    // Soundness: unmasked `x` (bits 8..63 unconstrained by 8-bit `pdep` mask `0x5555`) must NOT fold to `0xa5`!
    let out_full = Engine::standard()
        .run(&mut cx, &[sym_x], Run::default().with_assumptions(&assump))
        .unwrap();
    assert!(cx.as_const(out_full.roots[0].expr).unwrap().is_none());
}

#[test]
fn guarded_branch_invariant_select_and_wide_cofactors() {
    // 1. Symmetric `select(x == y, P(x), P(y)) -> P(y)` regardless of symbol order, across `16, 64, 256`.
    for w in [16u16, 64, 256] {
        assert_simplifies_to("select(x == y, x * x + 1, y * y + 1)", "y * y + 1", w);
        assert_simplifies_to("select(y == x, x * x + 1, y * y + 1)", "y * y + 1", w);
        assert_simplifies_to("select(x != y, y * y + 1, x * x + 1)", "y * y + 1", w);
        // Relational sum guard `a + b == 10`: `a * z + b * z == 10 * z` on the true branch!
        assert_simplifies_to("select(a + b == 10, a * z + b * z, 10 * z)", "10 * z", w);
        // Odd-affine guard `x * 5 + 3 == y`: `y * y` agrees with `(x * 5 + 3)^2` on the true branch!
        assert_simplifies_to(
            "select(x * 5 + 3 == y, y * y + 7, (x * 5 + 3) * (x * 5 + 3) + 7)",
            "(x * 5 + 3) * (x * 5 + 3) + 7",
            w,
        );
        // Bit-mask guard `(x & 1) == 0`: `x + 1 == x | 1` on the true branch -> `x | 1`!
        assert_simplifies_to("select((x & 1) == 0, x + 1, x | 1)", "x | 1", w);
        assert_simplifies_to("select((x & 0x0f) == 0, x + 0x0f, x | 0x0f)", "x | 0x0f", w);
    }
    // Verify `Engine::standard()` also folds 1-bit `Extract`-canonicalized guarded `select`.
    {
        let mut cx = Context::new();
        let opts = ParseOptions::width(Width::W64);
        let e = cx
            .parse("select((x & 1) == 0, x + 1, x | 1)", &opts)
            .unwrap();
        let out = Engine::standard().simplify(&mut cx, e).unwrap().expr;
        assert_eq!(out, cx.parse("x | 1", &opts).unwrap());
    }

    // 2. Soundness: non-agreeing branches MUST NOT collapse!
    let (mut cx, orig, simp) = assert_sound_nonconstant("select(x == y, x * x + 1, y * y + 2)", 64);
    assert_ne!(
        simp,
        cx.parse("y * y + 2", &ParseOptions::width(Width::W64))
            .unwrap()
    );
    let _ = assert_sound_nonconstant("select((x & 1) == 0, x + 3, x | 3)", 64);
    let env = [
        (
            SymbolKey::from("x"),
            BitVec::from_u64(Width::W64, 2).unwrap(),
        ),
        (
            SymbolKey::from("y"),
            BitVec::from_u64(Width::W64, 2).unwrap(),
        ),
    ];
    assert_eq!(
        cx.eval(&[orig], env.as_slice()).unwrap()[0],
        BitVec::from_u64(Width::W64, 5).unwrap()
    );

    // 3. Wide (`128`, `256`, `512`-bit) MBA cofactor cancellation!
    for w in [128u16, 256, 512] {
        assert_simplifies_to(
            "u * ((x ^ y) & z) * 3 + w + (u * 3) * ((x ^ y) & ~z) - (x ^ y) * (u * 3)",
            "w",
            w,
        );
        // `7*(x | y) + 7*(x & y) == 7*(x ^ y) + 14*(x & y)`: cancels completely leaving `z`.
        assert_simplifies_to(
            "(u * 7) * (x | y) + (u * 7) * (x & y) - (u * 7) * (x ^ y) - u * 14 * (x & y) + z",
            "z",
            w,
        );
    }
}
