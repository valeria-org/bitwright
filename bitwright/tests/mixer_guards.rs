//! Integration tests for 64-bit invertible mixer equation solving, bounded-domain completeness,
//! best-effort 64-bit witnesses, and the mixer bijection theory vs. free-symbol abstraction.
#![cfg(feature = "prove")]

use std::sync::Arc;

use bitwright::prove::mixer::{
    Domain, Equation, ExprWitness, Incomplete, Limits, SolveOutcome, System, WitnessLimits,
    WitnessOutcome, eval_round, extract_all_systems, extract_systems, fold_rounds, invert_odd_u64,
    invert_round, mk_round, propose_expr_witness, propose_witness, registry, simplify_predicate,
    solve_bounded, solve_derived,
};
use bitwright::prove::{self, Config, Outcome};
use bitwright::{Assumptions, BitVec, Context, ContextConfig, ParseOptions, SymbolKey, Width};

struct GroupCase {
    id: &'static str,
    pairs: &'static [(u64, u64, u64)],
    expected_small: Option<u64>,
}

const MEASURED_GROUPS: &[GroupCase] = &[
    GroupCase {
        id: "S1a",
        pairs: &[(
            0x3188_e5d3_9d63_b2d3,
            0x9b1d_b13a_6e8e_3927,
            0x661a_3797_479e_6265,
        )],
        expected_small: Some(0x33f8),
    },
    GroupCase {
        id: "S1b",
        pairs: &[
            (
                0x3188_e5d3_9d63_b2d3,
                0xd4a4_5b29_3511_446d,
                0x45e9_0472_d30c_bf2f,
            ),
            (
                0x3188_e5d3_9d63_b2d3,
                0x6c5c_ed13_4889_b257,
                0xc761_274b_f7a0_9cd5,
            ),
        ],
        expected_small: Some(0x33f8),
    },
    GroupCase {
        id: "S1c",
        pairs: &[
            (
                0x32d6_b9ab_66ee_96e5,
                0xdd9b_159a_5c9d_88a7,
                0x3268_a492_d30e_9949,
            ),
            (
                0xb952_a74c_7362_9447,
                0xdd9b_159a_5c9d_88a7,
                0xb82e_7328_896c_2d55,
            ),
        ],
        expected_small: None,
    },
    GroupCase {
        id: "S1d",
        pairs: &[
            (
                0x1937_5d6d_a745_962d,
                0x59b9_ad64_5ab1_3491,
                0x5e30_108a_5eea_4647,
            ),
            (
                0x3659_5ddb_1a69_14cd,
                0x59b9_ad64_5ab1_3491,
                0xaef2_b3e2_db24_a180,
            ),
        ],
        expected_small: None,
    },
    GroupCase {
        id: "S1e",
        pairs: &[
            (
                0x1a38_a692_ab8a_68d7,
                0x491d_a65a_c76e_9a59,
                0x8718_3662_700e_fac5,
            ),
            (
                0x1a38_a692_ab8a_68d7,
                0xe32e_ebaa_a6b4_4a73,
                0x33f3_1f2d_aaf5_c4e8,
            ),
            (
                0x1a38_a692_ab8a_68d7,
                0x32b4_7572_b359_2511,
                0x4c82_be63_351f_8a2e,
            ),
        ],
        expected_small: None,
    },
    GroupCase {
        id: "D1",
        pairs: &[
            (
                0x4ecb_31ce_ce39_6449,
                0x8a25_a2a6_916c_ee2f,
                0x3687_b292_01a8_7fff,
            ),
            (
                0x4ecb_31ce_ce39_6449,
                0xee34_e4cc_6a4c_5d6b,
                0x480f_95a9_f02a_a3fd,
            ),
        ],
        expected_small: None,
    },
    GroupCase {
        id: "D2",
        pairs: &[
            (
                0xaea4_cc6c_45d4_a489,
                0xea73_aac9_c9a7_452f,
                0xa2a6_8d2e_33d4_89de,
            ),
            (
                0x968a_38a8_db47_48a9,
                0xea73_aac9_c9a7_452f,
                0x64df_a538_6d94_bf0f,
            ),
        ],
        expected_small: None,
    },
    GroupCase {
        id: "D2n",
        pairs: &[
            (
                0x9224_a73a_b2e6_eca3,
                0x9656_748c_ab12_95b3,
                0x33c0_745e_2871_9084,
            ),
            (
                0x9656_748c_ab12_95b3,
                0xadad_7445_a551_3aa7,
                0x57d4_6632_7377_4658,
            ),
            (
                0x8d56_d3ad_95ae_6259,
                0x9656_748c_ab12_95b3,
                0xd9ed_7e6c_2e48_02b9,
            ),
        ],
        expected_small: Some(0xe),
    },
    GroupCase {
        id: "D2s",
        pairs: &[
            (
                0x3676_89cb_5a47_6369,
                0xe911_1d9d_4e2d_9567,
                0x51ee_7179_98d1_84d5,
            ),
            (
                0x3676_89cb_5a47_6369,
                0xe94e_dab5_c6a2_68bb,
                0x0c86_e3c1_86dc_f577,
            ),
            (
                0x3676_89cb_5a47_6369,
                0x52e9_69b8_da5a_3127,
                0xf21e_6b3e_adf2_c6e9,
            ),
        ],
        expected_small: Some(0),
    },
    GroupCase {
        id: "D3a",
        pairs: &[
            (
                0xd137_2d6c_ba57_1473,
                0xd234_e96e_b591_d467,
                0x3d5a_d4ef_ec8e_4dd9,
            ),
            (
                0xd137_2d6c_ba57_1473,
                0xe8d5_baa8_964d_6489,
                0x8cdd_38b3_3dde_441d,
            ),
            (
                0xd137_2d6c_ba57_1473,
                0xe923_1298_9631_4da3,
                0xb0b1_1786_8c0e_e9aa,
            ),
        ],
        expected_small: Some(0),
    },
    GroupCase {
        id: "D3b",
        pairs: &[(
            0x339d_176d_1262_346d,
            0x7257_7698_9898_b5db,
            0xc1f0_e031_5bf4_e3c3,
        )],
        expected_small: None,
    },
    GroupCase {
        id: "D3c",
        pairs: &[
            (
                0x6297_4629_2d26_8aa7,
                0xdcae_e56d_96d1_ca45,
                0xd025_aab1_ef65_7c4b,
            ),
            (
                0x6aa2_99b9_c8e8_adaf,
                0xdcae_e56d_96d1_ca45,
                0x787a_09da_3992_2d7f,
            ),
            (
                0xd539_45a2_c455_6d8b,
                0xdcae_e56d_96d1_ca45,
                0x7689_03ff_3f3f_f4f0,
            ),
        ],
        expected_small: Some(0),
    },
    GroupCase {
        id: "R1a",
        pairs: &[(
            0x44eb_9666_d744_d553,
            0xcd77_335a_edd2_2315,
            0xa24b_fba7_839e_4d09,
        )],
        expected_small: None,
    },
    GroupCase {
        id: "R1b",
        pairs: &[
            (
                0xcd77_335a_edd2_2315,
                0xdd4e_4b46_e9b4_9971,
                0x5921_396a_a102_00ae,
            ),
            (
                0x53a7_588c_9a59_3635,
                0xcd77_335a_edd2_2315,
                0x9928_a804_7afa_26f3,
            ),
        ],
        expected_small: None,
    },
];

fn system_from_pairs(pairs: &[(u64, u64, u64)]) -> System {
    System::new(
        pairs
            .iter()
            .map(|&(a, b, k)| Equation::new(vec![a, b], k))
            .collect::<Vec<_>>(),
    )
}

#[test]
fn measured_groups_match_best_effort_witness_and_fail_closed_on_64bit_secrets() {
    let limits = WitnessLimits::default();
    for g in MEASURED_GROUPS {
        let sys = system_from_pairs(g.pairs);
        let res = propose_witness(&sys, &limits);
        match g.expected_small {
            Some(expected) => match res {
                WitnessOutcome::Found { value, .. } => {
                    assert_eq!(value, expected, "group {} witness mismatch", g.id);
                    assert!(sys.holds(value));
                }
                other => panic!(
                    "group {} expected Found({expected:#x}), got {other:?}",
                    g.id
                ),
            },
            None => {
                assert!(
                    matches!(res, WitnessOutcome::Unknown { .. }),
                    "group {} should fail closed as Unknown, got {res:?}",
                    g.id
                );
            }
        }
    }
}

#[test]
fn expression_witness_inverts_odd_multiplier_and_narrow_cast_inputs() {
    let mut cx = Context::with_registry(ContextConfig::default(), Arc::new(registry()));
    // D2n: input is `counter * 0x5f4fe830eff60791`, where mixer input == 0xe!
    let counter = cx.symbol("counter", Width::W64).unwrap();
    let mult = cx.constant_u64(Width::W64, 0x5f4f_e830_eff6_0791).unwrap();
    let scaled = cx.mul(counter, mult).unwrap();
    let d2n_pairs = MEASURED_GROUPS
        .iter()
        .find(|g| g.id == "D2n")
        .unwrap()
        .pairs;
    let mut guard = cx.constant_u64(Width::W1, 1).unwrap();
    for &(a, b, k) in d2n_pairs {
        let ha = mk_round(&mut cx, scaled, a).unwrap();
        let hb = mk_round(&mut cx, scaled, b).unwrap();
        let xored = cx.xor(ha, hb).unwrap();
        // Spell with `+ (-K) == 0` like the faithful lowers!
        let neg_k = cx.constant_u64(Width::W64, k.wrapping_neg()).unwrap();
        let sum = cx.add(xored, neg_k).unwrap();
        let zero = cx.constant_u64(Width::W64, 0).unwrap();
        let eq = cx.cmp(bitwright::CmpOp::Eq, sum, zero).unwrap();
        guard = cx.and(guard, eq).unwrap();
    }

    let systems = extract_systems(&cx, guard, None).unwrap();
    assert_eq!(systems.len(), 1);
    assert_eq!(systems[0].input(), Some(scaled));

    let w = propose_expr_witness(&mut cx, &systems[0], None, &WitnessLimits::default()).unwrap();
    let expected_counter = 0xeu64.wrapping_mul(invert_odd_u64(0x5f4f_e830_eff6_0791).unwrap());
    match w {
        ExprWitness::Found {
            input_value,
            inner,
            inner_value,
            ..
        } => {
            assert_eq!(input_value, 0xe);
            assert_eq!(inner, counter);
            assert_eq!(inner_value.to_u64(), Some(expected_counter));
            assert_eq!(expected_counter.wrapping_mul(0x5f4f_e830_eff6_0791), 0xe);
        }
        other => panic!("expected ExprWitness::Found for D2n, got {other:?}"),
    }

    // Guard sampler inside `prove` also refutes `!guard` directly using the proposed patch!
    let not_guard = cx.not(guard).unwrap();
    match prove::valid(&mut cx, not_guard, &Config::default()).unwrap() {
        Outcome::Refuted(m) => {
            let found = m
                .iter()
                .find(|(k, _)| *k == SymbolKey::from("counter"))
                .and_then(|(_, v)| v.to_u64());
            assert_eq!(found, Some(expected_counter));
        }
        other => panic!("expected Refuted for !D2n, got {other:?}"),
    }
}

#[test]
fn complete_bounded_solving_is_deterministic_across_threads_and_domains() {
    let s1b = system_from_pairs(
        MEASURED_GROUPS
            .iter()
            .find(|g| g.id == "S1b")
            .unwrap()
            .pairs,
    );
    let dom_u16 = Domain::low_bits(16);
    let out_t1 = solve_bounded(
        &s1b,
        &dom_u16,
        &Limits::default().with_max_inputs(1 << 16).with_threads(1),
    );
    let out_t4 = solve_bounded(
        &s1b,
        &dom_u16,
        &Limits::default().with_max_inputs(1 << 16).with_threads(4),
    );
    assert_eq!(out_t1, out_t4);
    assert_eq!(
        out_t1,
        SolveOutcome::Complete {
            solutions: vec![0x33f8],
            evaluated: 1 << 16,
        }
    );

    // Fuel exhaustion is deterministic and fails closed (`Unknown`), never claiming completeness.
    let exhausted = solve_bounded(
        &s1b,
        &Domain::low_bits(32),
        &Limits::default().with_max_inputs(1 << 16).with_threads(4),
    );
    assert_eq!(
        exhausted,
        SolveOutcome::Unknown(Incomplete::FuelExhausted {
            required: 1u128 << 32,
            budget: 1 << 16,
        })
    );

    // Negative signed i16 value via `Domain::signed_bits(16)`:
    let neg_x = (-1234i64) as u64;
    let a = 0x4ecb_31ce_ce39_6449;
    let b = 0x8a25_a2a6_916c_ee2f;
    let c = 0xee34_e4cc_6a4c_5d6b;
    let sys_neg = System::new(vec![
        Equation::new(vec![a, b], eval_round(neg_x, a) ^ eval_round(neg_x, b)),
        Equation::new(vec![a, c], eval_round(neg_x, a) ^ eval_round(neg_x, c)),
    ]);
    let res_sext16 = solve_bounded(
        &sys_neg,
        &Domain::signed_bits(16),
        &Limits::default().with_max_inputs(1 << 16).with_threads(4),
    );
    assert_eq!(
        res_sext16,
        SolveOutcome::Complete {
            solutions: vec![neg_x],
            evaluated: 1 << 16,
        }
    );
}

#[test]
fn derive_domain_handles_zext_sext_masks_shifts_and_assumptions() {
    let mut cx = Context::new();
    let opts64 = ParseOptions::width(Width::W64);

    // 1. Sign-extended i32 (`sext<64>(s32)`): KnownBits and URange are 2^64, but SRange is 2^32!
    let sext_expr = cx.parse("sext<64>(s:32)", &opts64).unwrap();
    let d_sext = Domain::derive(&mut cx, sext_expr, None).unwrap();
    assert_eq!(d_sext.len(), 1u128 << 32);

    // 2. Zero-extended u16 (`zext<64>(u:16)`): size 2^16.
    let zext_expr = cx.parse("zext<64>(u:16)", &opts64).unwrap();
    let d_zext = Domain::derive(&mut cx, zext_expr, None).unwrap();
    assert_eq!(d_zext.len(), 1u128 << 16);

    // 3. Right-shifted 64-bit word (`call_res >>u 48`), mirrored after D3c (`>>u 37`):
    let shifted = cx
        .parse("(raw:64 >>u 48) * 0x6c9a72db55850a43", &opts64)
        .unwrap();
    let d_shifted = Domain::derive(&mut cx, shifted, None).unwrap();
    assert_eq!(d_shifted.len(), 1u128 << 16);

    let x_true = 0x1234u64.wrapping_mul(0x6c9a_72db_5585_0a43);
    let k1 = 0x6297_4629_2d26_8aa7;
    let k2 = 0xdcae_e56d_96d1_ca45;
    let k3 = 0x6aa2_99b9_c8e8_adaf;
    let sys = System::for_input(
        shifted,
        vec![
            Equation::new(
                vec![k1, k2],
                eval_round(x_true, k1) ^ eval_round(x_true, k2),
            ),
            Equation::new(
                vec![k2, k3],
                eval_round(x_true, k2) ^ eval_round(x_true, k3),
            ),
        ],
    );
    let (derived, solved) = solve_derived(
        &mut cx,
        &sys,
        None,
        &Limits::default().with_max_inputs(1 << 16).with_threads(2),
    )
    .unwrap();
    assert_eq!(derived.len(), 1u128 << 16);
    assert_eq!(
        solved,
        SolveOutcome::Complete {
            solutions: vec![x_true],
            evaluated: 1 << 16,
        }
    );

    // 4. Scoped Assumptions tighten an unconstrained 64-bit symbol to `[0x1000, 0x1fff]`:
    let range_pred = cx
        .parse(
            "(0x1000 <=u bounded_sym:64) & (bounded_sym <=u 0x1fff)",
            &ParseOptions::width(Width::W1),
        )
        .unwrap();
    let sym = cx.symbol("bounded_sym", Width::W64).unwrap();
    let mut assump = Assumptions::new();
    assump.assume_true(&mut cx, range_pred).unwrap();
    let d_assump = Domain::derive(&mut cx, sym, Some(&assump)).unwrap();
    assert_eq!(d_assump.len(), 0x1000);
}

#[test]
fn mixer_theory_decides_guard_combinations_that_free_symbols_leave_open() {
    // Compare written-out / `@mixer.round` mixer theory against vulture's free-symbol lowering.
    let mut cx = Context::with_registry(ContextConfig::default(), Arc::new(registry()));
    let x = cx.symbol("x", Width::W64).unwrap();
    let y = cx.symbol("y", Width::W64).unwrap();
    let a = 0x3188_e5d3_9d63_b2d3u64;
    let b = 0x9b1d_b13a_6e8e_3927u64;
    let c = 0xd4a4_5b29_3511_446du64;

    let hx_a = mk_round(&mut cx, x, a).unwrap();
    let hy_a = mk_round(&mut cx, y, a).unwrap();
    let hx_b = mk_round(&mut cx, x, b).unwrap();
    let hy_b = mk_round(&mut cx, y, b).unwrap();
    let hx_c = mk_round(&mut cx, x, c).unwrap();

    // Case 1: Same-key injectivity `(H(x, a) == H(y, a)) <=> (x == y)`
    let eq_h = cx.cmp(bitwright::CmpOp::Eq, hx_a, hy_a).unwrap();
    let eq_xy = cx.cmp(bitwright::CmpOp::Eq, x, y).unwrap();
    let iff_inj = cx.cmp(bitwright::CmpOp::Eq, eq_h, eq_xy).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, iff_inj, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));

    // Free-symbol abstraction (`free_hx_a == free_hy_a <=> x == y`) cannot prove this (`Refuted`)!
    let free_hx = cx.symbol("free_hx", Width::W64).unwrap();
    let free_hy = cx.symbol("free_hy", Width::W64).unwrap();
    let free_eq = cx.cmp(bitwright::CmpOp::Eq, free_hx, free_hy).unwrap();
    let free_iff = cx.cmp(bitwright::CmpOp::Eq, free_eq, eq_xy).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, free_iff, &Config::default()).unwrap(),
        Outcome::Refuted(_)
    ));

    // Case 2: Single-round impossible range `!(H(zext<64>(u32_sym), a) == K)` when `unhash(K, a) >= 2^32`
    let u32_sym = cx.symbol("u32_sym", Width::W32).unwrap();
    let z64 = cx.zext(u32_sym, Width::W64).unwrap();
    let hz = mk_round(&mut cx, z64, a).unwrap();
    let k_hi = eval_round(0x1_0000_1234u64, a);
    assert_eq!(invert_round(k_hi, a), Some(0x1_0000_1234));
    let k_hi_expr = cx.constant_u64(Width::W64, k_hi).unwrap();
    let impossible_1 = cx.cmp(bitwright::CmpOp::Ne, hz, k_hi_expr).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, impossible_1, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));

    // Case 3: 3-pair GF(2) triangle implication over unrestricted 64-bit `x`:
    // `(H(x,a)^H(x,b) == K1) & (H(x,b)^H(x,c) == K2) => (H(x,a)^H(x,c) == K1 ^ K2)`
    // Note: free-symbol lowering ALSO gets pure XOR transitivity when the SAME round nodes are shared,
    // EXCEPT when one round is written with an equal input `y` (`x == y`)!
    let k1 = eval_round(0x7777, a) ^ eval_round(0x7777, b);
    let k2 = eval_round(0x7777, b) ^ eval_round(0x7777, c);
    let k1_e = cx.constant_u64(Width::W64, k1).unwrap();
    let k2_e = cx.constant_u64(Width::W64, k2).unwrap();
    let k3_e = cx.constant_u64(Width::W64, k1 ^ k2).unwrap();
    let xab = cx.xor(hx_a, hx_b).unwrap();
    let ybc = cx.xor(hy_b, hx_c).unwrap();
    let xac = cx.xor(hx_a, hx_c).unwrap();
    let p_xy = cx.cmp(bitwright::CmpOp::Eq, x, y).unwrap();
    let p_1 = cx.cmp(bitwright::CmpOp::Eq, xab, k1_e).unwrap();
    let p_2 = cx.cmp(bitwright::CmpOp::Eq, ybc, k2_e).unwrap();
    let concl = cx.cmp(bitwright::CmpOp::Eq, xac, k3_e).unwrap();
    let prem = cx.and(p_xy, p_1).unwrap();
    let prem = cx.and(prem, p_2).unwrap();
    let not_prem = cx.not(prem).unwrap();
    let goal_congr = cx.or(not_prem, concl).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, goal_congr, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));
    // And with a wrong target `K1 ^ K2 ^ 1`, the implication is NOT valid (`Refuted` at `x = y = 0x7777`)!
    let k3_bad = cx.constant_u64(Width::W64, k1 ^ k2 ^ 1).unwrap();
    let concl_bad = cx.cmp(bitwright::CmpOp::Eq, xac, k3_bad).unwrap();
    let goal_congr_bad = cx.or(not_prem, concl_bad).unwrap();
    assert!(!matches!(
        prove::valid(&mut cx, goal_congr_bad, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));

    // Case 4: Mixed 1-hash + pair `(H(x, a) == H(x0, a)) => ((H(x, a) ^ H(x, b)) == (H(x0, a) ^ H(x0, b)))`
    // over unrestricted 64-bit `x`! Free symbols leave `H(x, b)` completely unconstrained!
    let ha_val = cx
        .constant_u64(Width::W64, eval_round(0xdead_beef_cafe_1234, a))
        .unwrap();
    let hab_val = cx
        .constant_u64(
            Width::W64,
            eval_round(0xdead_beef_cafe_1234, a) ^ eval_round(0xdead_beef_cafe_1234, b),
        )
        .unwrap();
    let g_single = cx.cmp(bitwright::CmpOp::Eq, hx_a, ha_val).unwrap();
    let g_pair = cx.cmp(bitwright::CmpOp::Eq, xab, hab_val).unwrap();
    let not_single = cx.not(g_single).unwrap();
    let mixed_imp = cx.or(not_single, g_pair).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, mixed_imp, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));

    // Case 5: Complete bounded-domain refutation inside `prove`:
    // On an 8-bit zero-extended input `zext<64>(b:8)`, an unreachable pair target `K = 1` is proved false!
    let b8 = cx.symbol("b8", Width::W8).unwrap();
    let zb8 = cx.zext(b8, Width::W64).unwrap();
    let hb_a = mk_round(&mut cx, zb8, a).unwrap();
    let hb_b = mk_round(&mut cx, zb8, b).unwrap();
    let hb_xor = cx.xor(hb_a, hb_b).unwrap();
    let one64 = cx.constant_u64(Width::W64, 1).unwrap();
    let ne_one = cx.cmp(bitwright::CmpOp::Ne, hb_xor, one64).unwrap();
    assert!(matches!(
        prove::valid(&mut cx, ne_one, &Config::default()).unwrap(),
        Outcome::Proved(_)
    ));
}

#[test]
fn round_trip_unround_and_written_out_folding_preserve_semantics() {
    let reg = Arc::new(registry());
    let mut cx = Context::with_registry(ContextConfig::default(), reg.clone());
    let unround_id = reg.id("mixer.unround").unwrap();

    // Written-out round parsed from text folds to `@mixer.round`, and `@mixer.unround` cancels it!
    let written = cx
        .parse(
            "let %0 = (x:64 ^ 0x3188e5d39d63b2d3) * 0x3188e5d39d63b2d3; \
             (%0 ^ %0 >>u 32 >>u (%0 >>u 60)) * 0x3188e5d39d63b2d3",
            &ParseOptions::width(Width::W64),
        )
        .unwrap();
    let folded = fold_rounds(&mut cx, written).unwrap();
    let key = cx.constant_u64(Width::W64, 0x3188_e5d3_9d63_b2d3).unwrap();
    let unrounded = cx.ext(unround_id, &[folded, key]).unwrap()[0];
    let x = cx.symbol("x", Width::W64).unwrap();
    let eq = cx.cmp(bitwright::CmpOp::Eq, unrounded, x).unwrap();
    let simplified = simplify_predicate(&mut cx, eq, None, 0).unwrap();
    assert_eq!(
        cx.as_const(simplified).unwrap().and_then(|v| v.to_u64()),
        Some(1)
    );
}

#[test]
fn s1_faithful_jump_expression_extracts_witness_and_resolves_taken_target() {
    let s1_expr = "\
let %0 = (#44241:64 ^ 0x32d6b9ab66ee96e5) * 0x32d6b9ab66ee96e5;
let %1 = (#44241 ^ 0xdd9b159a5c9d88a7) * 0xdd9b159a5c9d88a7;
let %2 = (%1 ^ %1 >>u 32 >>u (%1 >>u 60)) * 0xdd9b159a5c9d88a7;
let %3 = (#44241 ^ 0xb952a74c73629447) * 0xb952a74c73629447;
let %4 = (#44241 ^ 0x698e48ee4ca56d89) * 0x698e48ee4ca56d89;
let %5 = zext<64>(zext<32>((%0 ^ %0 >>u 32 >>u (%0 >>u 60)) * 0x32d6b9ab66ee96e5 ^ %2 ^ 0x3268a492d30e9949 | %2 ^ (%3 ^ %3 >>u 32 >>u (%3 >>u 60)) * 0xb952a74c73629447 ^ 0xb82e7328896c2d55 == 0) & zext<32>(((%4 ^ %4 >>u 32 >>u (%4 >>u 60)) * 0x698e48ee4ca56d89 ^ %2) + 0xaf5045f4c029c7b3 == 0));
let %6 = (#44241 ^ 0xadab52a5d6a57397) * 0xadab52a5d6a57397;
let %7 = (((%6 ^ %6 >>u 32 >>u (%6 >>u 60)) * 0xadab52a5d6a57397 ^ %2) + 0x3584656e8524cf4f) * %5;
let %8 = %7 * -1;
let %9 = #44270:64 & 0xd6d480358fdbc106 | 0x23550a40043669;
let %10 = 0x6418551bebaa279f <=u %9;
let %11 = zext<64>(zext<32>(%10) & trunc<32>(%9));
let %12 = (%8 + 0x9f87aa9b120a5a49) * %11;
let %13 = (#44253:64 ^ 0x9654c94ab99ad6ed) * 0x9654c94ab99ad6ed;
let %14 = (#44253 ^ 0x59b9ad645ab13491) * 0x59b9ad645ab13491;
let %15 = (%14 ^ %14 >>u 32 >>u (%14 >>u 60)) * 0x59b9ad645ab13491;
let %16 = %12 * -1;
let %17 = (#44253 ^ 0x36595ddb1a6914cd) * 0x36595ddb1a6914cd;
let %18 = (#44253 ^ 0x19375d6da745962d) * 0x19375d6da745962d;
let %19 = (#44253 ^ 0xed62d53699a6ace9) * 0xed62d53699a6ace9;
let %20 = zext<64>(zext<32>(zext<8>((%17 ^ %17 >>u 32 >>u (%17 >>u 60)) * 0x36595ddb1a6914cd ^ %15 ^ 0xaef2b3e2db24a180 | (%18 ^ %18 >>u 32 >>u (%18 >>u 60)) * 0x19375d6da745962d ^ %15 ^ 0x5e30108a5eea4647 == 0) & zext<8>(%10)) & zext<32>(((%19 ^ %19 >>u 32 >>u (%19 >>u 60)) * 0xed62d53699a6ace9 ^ %15) + 0x14e6580d5c7d4834 == 0));
let %21 = (%8 + ((%13 ^ %13 >>u 32 >>u (%13 >>u 60)) * 0x9654c94ab99ad6ed ^ %15) + %16 + 0xcf9a0f91d6b43206) * %20;
let %22 = %16 + %8 + %21 * -1;
let %23 = 0x78748961aa2ceecf <=u %9;
let %24 = zext<64>(zext<8>(%23) & trunc<8>(%9));
let %25 = (%22 + 0x20f92ceec5fe0a3) * %24;
let %26 = %5 * 0x318c8a43b48e06cc;
let %27 = (%26 + 0x60785564edf1bbbd) * %11;
let %28 = %27 * -1 + %26;
let %29 = (%28 + 0x48427f81390d4d71) * %20;
let %30 = %28 + %29 * -1;
let %31 = (%30 + 0xfdf06d31139df4d7) * %24;
let %32 = (#44267:64 ^ 0x3188e5d39d63b2d3) * 0x3188e5d39d63b2d3;
let %33 = (%32 ^ %32 >>u 32 >>u (%32 >>u 60)) * 0x3188e5d39d63b2d3;
let %34 = (#44267 ^ 0x1a957362c8dbad2d) * 0x1a957362c8dbad2d;
let %35 = (#44267 ^ 0xd4a45b293511446d) * 0xd4a45b293511446d;
let %36 = (#44267 ^ 0x6c5ced134889b257) * 0x6c5ced134889b257;
let %37 = (#44267 ^ 0x9b1db13a6e8e3927) * 0x9b1db13a6e8e3927;
let %38 = (#49003:64 ^ 0x1a38a692ab8a68d7) * 0x1a38a692ab8a68d7;
let %39 = (%38 ^ %38 >>u 32 >>u (%38 >>u 60)) * 0x1a38a692ab8a68d7;
let %40 = (#49003 ^ 0xe32eebaaa6b44a73) * 0xe32eebaaa6b44a73;
let %41 = (#49003 ^ 0x491da65ac76e9a59) * 0x491da65ac76e9a59;
let %42 = (#49003 ^ 0x32b47572b3592511) * 0x32b47572b3592511;
let %43 = zext<64>((zext<32>(%33 ^ (%35 ^ %35 >>u 32 >>u (%35 >>u 60)) * 0xd4a45b293511446d ^ 0x45e90472d30cbf2f | %33 ^ (%36 ^ %36 >>u 32 >>u (%36 >>u 60)) * 0x6c5ced134889b257 ^ 0xc761274bf7a09cd5 == 0) & zext<32>(%33 ^ (%37 ^ %37 >>u 32 >>u (%37 >>u 60)) * 0x9b1db13a6e8e3927 ^ 0x661a3797479e6265 == 0) | zext<32>(%39 ^ (%40 ^ %40 >>u 32 >>u (%40 >>u 60)) * 0xe32eebaaa6b44a73 ^ 0x33f31f2daaf5c4e8 | %39 ^ (%41 ^ %41 >>u 32 >>u (%41 >>u 60)) * 0x491da65ac76e9a59 ^ 0x87183662700efac5 | %39 ^ (%42 ^ %42 >>u 32 >>u (%42 >>u 60)) * 0x32b47572b3592511 ^ 0x4c82be63351f8a2e == 0)) & zext<32>(%23));
%5 * 0xce7375bc4b71f934 + %7 + %12 + %21 + %25 + %27 + %29 + %31 + (%22 + %25 * -1 + (%33 ^ (%34 ^ %34 >>u 32 >>u (%34 >>u 60)) * 0x1a957362c8dbad2d) + 0x30b8aad8d8ef302d) * %43 + (%30 + %31 * -1 + 0x1eb15b00437e0a8d) * %43 + 0x14047a256";

    let mut cx = Context::new();
    let target = cx.parse(s1_expr, &ParseOptions::width(Width::W64)).unwrap();
    let systems = extract_all_systems(&cx, target).unwrap();
    assert_eq!(systems.len(), 4);

    let sym_44267 = cx.symbol(SymbolKey::from(44267u64), Width::W64).unwrap();
    let sys_44267 = systems
        .iter()
        .find(|s| s.input() == Some(sym_44267))
        .expect("system for #44267");
    let witness =
        propose_expr_witness(&mut cx, sys_44267, None, &WitnessLimits::default()).unwrap();
    match witness {
        ExprWitness::Found {
            input_value: 0x33f8,
            inner,
            inner_value,
            ..
        } => {
            assert_eq!(inner, sym_44267);
            assert_eq!(inner_value.to_u64(), Some(0x33f8));
        }
        other => panic!("expected 0x33f8 for #44267, got {other:?}"),
    }

    // Specializing #44267 = 0x33f8 (with #44270 = u64::MAX so %23 == 1, and #44241=#44253=#49003=0)
    // collapses the taken jump target to handler address `0x14039bc71`!
    let env = [
        (SymbolKey::from(44241u64), BitVec::zero(Width::W64)),
        (SymbolKey::from(44253u64), BitVec::zero(Width::W64)),
        (
            SymbolKey::from(44267u64),
            BitVec::from_u64(Width::W64, 0x33f8).unwrap(),
        ),
        (
            SymbolKey::from(44270u64),
            BitVec::from_u64(Width::W64, u64::MAX).unwrap(),
        ),
        (SymbolKey::from(49003u64), BitVec::zero(Width::W64)),
    ];
    let eval = cx.eval(&[target], &env[..]).unwrap()[0];
    assert_eq!(eval.to_u64(), Some(0x14039bc71));
}

#[test]
#[ignore = "heavy: complete 2^32-input bounded-domain verification and optional faithful replay timing; run with --release -- --ignored --nocapture"]
fn complete_u32_domains_and_faithful_replay_measurements() {
    use std::time::Instant;

    let threads = std::thread::available_parallelism()
        .map(std::num::NonZero::get)
        .unwrap_or(4);

    // 1. Complete 2^32 zext(u32) solve on S1b (unique solution 0x33f8) and D1 (empty in u32).
    let s1b = system_from_pairs(
        MEASURED_GROUPS
            .iter()
            .find(|g| g.id == "S1b")
            .unwrap()
            .pairs,
    );
    let t0 = Instant::now();
    let s1b_u32 = solve_bounded(
        &s1b,
        &Domain::low_bits(32),
        &Limits::default()
            .with_max_inputs(1u64 << 32)
            .with_threads(threads),
    );
    let s1b_ms = t0.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(
        s1b_u32,
        SolveOutcome::Complete {
            solutions: vec![0x33f8],
            evaluated: 1u64 << 32,
        }
    );
    println!("complete u32 S1b ({threads} threads): {s1b_ms:.2} ms -> [0x33f8]");

    let d1 = system_from_pairs(MEASURED_GROUPS.iter().find(|g| g.id == "D1").unwrap().pairs);
    let t1 = Instant::now();
    let d1_u32 = solve_bounded(
        &d1,
        &Domain::low_bits(32),
        &Limits::default()
            .with_max_inputs(1u64 << 32)
            .with_threads(threads),
    );
    let d1_ms = t1.elapsed().as_secs_f64() * 1000.0;
    assert_eq!(
        d1_u32,
        SolveOutcome::Complete {
            solutions: Vec::new(),
            evaluated: 1u64 << 32,
        }
    );
    println!("complete u32 D1  ({threads} threads): {d1_ms:.2} ms -> []");

    // 2. Optional per-file faithful replay report when BITWRIGHT_FAITHFUL_DIR is provided.
    if let Ok(dir) = std::env::var("BITWRIGHT_FAITHFUL_DIR") {
        let mut entries: Vec<_> = std::fs::read_dir(&dir)
            .unwrap()
            .filter_map(Result::ok)
            .map(|e| e.path())
            .filter(|p| p.extension().and_then(|s| s.to_str()) == Some("txt"))
            .collect();
        entries.sort();
        for path in entries {
            let name = path.file_name().unwrap().to_string_lossy().into_owned();
            let raw = std::fs::read_to_string(&path).unwrap();
            let body: String = raw
                .lines()
                .filter(|l| !l.trim_start().starts_with('#'))
                .collect::<Vec<_>>()
                .join("\n");
            let mut cx = Context::with_registry(ContextConfig::default(), Arc::new(registry()));
            let root = cx.parse(&body, &ParseOptions::width(Width::W64)).unwrap();

            let t_start = Instant::now();
            let systems = extract_all_systems(&cx, root).unwrap();
            let mut summaries = Vec::new();
            for sys in &systems {
                let w =
                    propose_expr_witness(&mut cx, sys, None, &WitnessLimits::default()).unwrap();
                let (dom, bounded) = solve_derived(
                    &mut cx,
                    sys,
                    None,
                    &Limits::default()
                        .with_max_inputs(1u64 << 27)
                        .with_threads(threads),
                )
                .unwrap();
                summaries.push(format!(
                    "eqs={} dom_len=2^{:.1} bounded={bounded:?} witness={w:?}",
                    sys.equations().len(),
                    (dom.len() as f64).log2(),
                ));
            }
            let elapsed_ms = t_start.elapsed().as_secs_f64() * 1000.0;
            let folded = fold_rounds(&mut cx, root).unwrap();
            let orig_nodes = cx.dag_size(&[root], u32::MAX - 1).unwrap();
            let folded_nodes = cx.dag_size(&[folded], u32::MAX - 1).unwrap();
            println!(
                "FILE {name}: mixer_api={elapsed_ms:.3} ms systems={} dag={orig_nodes:?}->{folded_nodes:?}",
                systems.len()
            );
            for s in summaries {
                println!("  - {s}");
            }
        }
    }
}
