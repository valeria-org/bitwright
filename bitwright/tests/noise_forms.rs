#![cfg(feature = "mba")]

/// off (`MbaConfig::noise_forms`), and whether the result agrees with `text` at a grid of points
/// (each symbol 0, 1, 2, 52, 0xff or all ones).
fn noise_forms(text: &str, on: bool) -> (String, bool) {
    with_mba(
        text,
        ::bitwright::mba::MbaConfig::default().with_noise_forms(on),
    )
}

/// [`noise_forms`] with the MBA phase configured by `cfg`.
fn with_mba(text: &str, cfg: ::bitwright::mba::MbaConfig) -> (String, bool) {
    use ::bitwright::engine::{Engine, Run, Strategy};
    use ::bitwright::{BitVec, Context, FnEnv, ParseOptions, SymbolKey, Width};
    let engine = Engine::builder()
        .builtin()
        .strategy(Strategy::deobfuscate().with_mba(cfg))
        .build()
        .expect("an engine");
    let mut cx = Context::new();
    let e = cx
        .parse(text, &ParseOptions::width(Width::W64))
        .unwrap_or_else(|err| panic!("{text}: {err}"));
    let r = engine
        .run(&mut cx, &[e], Run::default())
        .expect("a run")
        .roots[0]
        .expr;
    let values = [0u64, 1, 2, 52, 0xff, u64::MAX];
    let mut agrees = true;
    for i in 0..values.len() * values.len() {
        let env = FnEnv(move |k: &SymbolKey, w: Width| {
            let pick = match format!("{k:?}").as_str() {
                s if s.contains("\"x\"") => i % values.len(),
                _ => i / values.len(),
            };
            Some(BitVec::wrapping_from_u64(w, values[pick]))
        });
        let v = cx.eval(&[e, r], &env).expect("an evaluation");
        agrees &= v[0] == v[1];
    }
    (cx.display(r).to_string(), agrees)
}

#[test]
fn a_rotate_spelled_as_its_shifts_beside_it_is_read_as_one_value() {
    // `rotl(t, 32) >>u 30` and `rotl(t, 32) << 34` are the low 34 and high 30 bits of
    // `rotl(t, 2)`, beside it in an MBA that cancels: three unrelated atoms as written.
    let text = "let t = x + 0xd7ae41bcb1c1992c; let r = rotl(t, 32); let lo = r >>u 30; \
                let hi = r << 34; let a = (lo | 0x8d49e7e8b8753b4a) & hi; \
                let b = hi & 0x8d49e7e8b8753b4a; \
                (~(lo ^ 0x72b61817478ac4b5) & hi) * 3 + (lo & 0x72b61817478ac4b5 | hi) \
                + (rotl(t, 2) & 0x8d49e7e8b8753b4a) - (a + a) - (b + b)";
    // The MBA phase reads the slices of one rotation as that rotation whatever its
    // configuration: with the noise forms or without.
    for forms in [true, false] {
        assert_eq!(
            noise_forms(text, forms),
            ("rotl(x + 0xd7ae41bcb1c1992c, 2)".to_owned(), true)
        );
    }
}

#[test]
fn what_a_condition_fixes_is_read_in_what_it_guards() {
    // A case of a table over noise: `c` is 1 whenever `x & 52 == 32`.
    let c = "let n = ~x; let a = (x | 0xd8458c0f66da983e) & -53; let b = ~(x & -53); \
             let d = n & 0x27ba73f0992567f5; \
             let s = a * 0x43c5f6be60dd5967 + n * 0x43c5f6be60dd5967 \
                 + b * 0xbc3a09419f22a699 + d * 0x43c5f6be60dd5967; \
             let p = s + 0x79099d14f9110c8e; let q = trunc<32>(p); \
             let m = n * 0x2851be434e3e66d4 + a * 0x2851be434e3e66d4 \
                 + b * 0xd7ae41bcb1c1992c + d * 0x2851be434e3e66d4 \
                 + rotl(0x5a67342ec19c550 << zext<64>(trunc<6>(q * 0xc4bee632)) \
                     | 0x5a67342ec19c550 >>u zext<64>(trunc<6>(q * -114)), 32) \
                 + 0x65130d5a2c1682a8; \
             let k = s + (p << 3) + 0x79099d14f9110c8e & 0xffffffff; \
             let c = ~(m << (k + (k << 2) & 63) | m >>u zext<64>(trunc<6>(q * -109))) \
                 >>u 57 & 1 == 1;";
    let guard = "(x & 52 == 32) & (trunc<8>(y) == 0)";
    for text in [
        format!("{c} {guard} & c"),
        format!("{c} c & ({guard})"),
        format!("{c} select({guard}, zext<64>(c), 0)"),
    ] {
        let (out, agrees) = noise_forms(&text, true);
        assert!(agrees, "{text}\n= {out}");
        assert!(!out.contains("rotl"), "{text}\n= {out}");
    }
}

#[test]
fn only_one_side_of_a_conjunction_reads_the_other_s_facts() {
    // Both sides rewritten under each other's facts would make this 1 at `x = 1, y = 0`.
    let (out, agrees) = noise_forms("(x == 0) & ((y == 0) & (x == 0))", true);
    assert!(agrees, "{out}");
}

#[test]
fn a_piece_that_depends_on_one_condition_is_read_as_its_cases() {
    // The piece is `0x8000001` where `trunc<32>(x) == 0` and 0 elsewhere, but no pass
    // evaluates the rotate on either side of the select under it.
    let text = "let c = trunc<32>(x) == 0; \
                let r = rotl(select(c, 0, 0x57b490accf633db0) + 0xec502a030056cb7d, 51); \
                zext<64>(~extract<23, 32>(r + 0x416bf12db336dc49) & 0x28200401) + y";
    let (out, agrees) = noise_forms(text, true);
    assert!(agrees, "{out}");
    assert!(!out.contains("rotl"), "{out}");
    assert!(noise_forms(text, false).0.contains("rotl"));
}

#[test]
fn a_condition_and_its_complement_are_one_case() {
    // `s` is 0 wherever `c` and its complement disagree, as they always do; read as two
    // conditions, the cases where both or neither hold make it `k`.
    let text = "let k = 0x123456789abcdef0; \
                let s = select(trunc<32>(x) == 0, 0, k) ^ select(trunc<32>(x) != 0, k, 0); \
                (rotl(s + 0x9e3779b97f4a7c15, 7) & 0xff00ff00ff) + y";
    assert_eq!(
        noise_forms(text, true),
        ("y + 0xbf003e00cf".to_owned(), true)
    );
    assert_ne!(noise_forms(text, false).0, "y + 0xbf003e00cf");
}

#[test]
fn bits_that_conditions_place_keep_their_spelling() {
    // An obfuscated stack address computed through a flags word
    // (`zext(c1) << 2 | 2 | zext(c2) << 6 | zext(c3) << 7`). Written as a table of its cases,
    // the word hides its bits from the MBA phase, and the address no longer folds.
    let text = "let %0 = #378 ^ 0x7ffe00000de0; \
                let %1 = #421 & 0x3c7300 | (zext<64>(popcnt(%0 & 255) & 1 == 0) << 2 | 2 | zext<64>(%0 == 0) << 6 | zext<64>(%0 <s 0) << 7); \
                let %2 = ~%1; \
                let %3 = ~(~((~(~zext<64>(#27467) & 0x646fea5fffceeffa) & 0xffd215be727f3faf) << 22) & 0xffffffffffd91bfa) + 0x624f41640548d4e3; \
                let %4 = ~(~%3 & 0x451e1d31ba270fe9) & ~(%3 & 0xbae1e2ce45d8f016); \
                let %5 = ~(%4 & 0x892b007476480f3d) & ~(~%4 & 0x76d4ff8b89b7f0c2); \
                let %6 = %2 & %5; \
                let %7 = ~(%5 & %1); \
                let %8 = ~%5; \
                let %9 = %7 & ~(%8 & %2); \
                let %10 = ~(~%6 * 0xccccccccccccccce + %2 * 0x3333333333333333 + %6 * 0x6666666666666667 + %7 * 0x9999999999999999 + (%8 & %1) * 0x9999999999999998 + %9 + %5 * 0xcccccccccccccccd + ~%9 * 0x6666666666666666 << 31); \
                let %11 = %10 * 0x35e907aa7be8eef9 + (%10 & 0xffffffff833d2876) * 0xca16f85584171106 + 0xd7baf5c2df0a0ec6; \
                let %12 = ~%11; \
                let %13 = %12 & 0xffff800000010000; \
                let %14 = %12 & 0x7ffffffeffff; \
                ~(~(%11 & 0x7ffffffeffff) & ~%13) + %13 + %14 + (%14 << 1) + %12 * -2";
    assert_eq!(
        noise_forms(text, true),
        ("0x7ffffffeffff:64".to_owned(), true)
    );
}

#[test]
fn an_opaque_constant_through_its_atoms_known_bits_is_proved_one() {
    // `%0` has its low byte 0 and `%2` its low byte 0x52 (the 82 the noise ORs in); under the
    // bitwise operators those bytes make the sums cancel. Read as free atoms they do not, and
    // the engine leaves all 66 nodes at any budget.
    let text = "let %0 = (x & 0xffffffff00000000) * 0x8000001 + 0xc00081fe00001000; \
                let %1 = %0 ^ -256; \
                let %2 = rotl((rotl(y, 5) & 0x1070a8a3c0) + 0x31d3e17cbbc89d2e, 2) * 0x20000001 + 0x315e13f6658a519a; \
                let %3 = ~%1 ^ (%2 | %1); \
                let %4 = ~%0; \
                let %5 = %4 | %2 ^ 255; \
                let %6 = %4 & -83; \
                ~(%3 * 0xaa9198db70383e98 + %5 * 0xaa9198db70383e98 + %6 * 0x556e67248fc7c168 & ((z & 255 | w & -256) + 0x4bc330b0be287ad4 ^ %3 * 0xd2fe010764f7e887 + %5 * 0xd2fe010764f7e887 + %6 * 0x2d01fef89b081779)) & (%0 | 82) * 0x556e67248fc7c169 + %5 * 0x556e67248fc7c169 - (%2 ^ %2 & %1) * 0x556e67248fc7c169";
    let cfg = ::bitwright::mba::MbaConfig::default();
    let (out, agrees) = with_mba(text, cfg.with_known_atoms(true));
    assert!(agrees, "{out}");
    assert!(out.starts_with("0xaa9198db70383e97"), "{out}");
    assert!(!with_mba(text, cfg).0.starts_with("0xaa9198db70383e97"));
}

#[test]
fn a_constant_through_one_condition_is_proved_on_either_side_of_it() {
    // What the engine leaves of a difficult case-split question: every select tests
    // `trunc<32>(x) == 0`. On one side the selects pick constants and the value is
    // 0xaa9198db70383e97; on the other the low half of `x` is 0 and the noise cancels through its
    // atoms' known bytes (see the test above).
    let text = "let %0 = trunc<32>(x); \
                let %1 = %0 == 0; \
                let %2 = select(%1, 0x20000001:64, 0); \
                let %3 = select(%1, 0x8000001:64, 0) * x + %2 * select(%0 != 0, select(#31422 == 0, 0x7ffe00000fd0, 0x272cc0a97cf728b9 - (zext<64>(#15245) ^ #1882) & 0x733aee9efdf41bcd ^ 0x10c97ea71d859fbe), 0x7ffe00001000); \
                let %4 = select(%1, 0:64, 1) * #12; \
                let %5 = %3 | %4; \
                let %6 = %5 ^ -256; \
                let %7 = rotl((rotl(#408, 5) & 0x1070a8a3c0) + 0x31d3e17cbbc89d2e, 2) * %2 + select(%1, 0x315e13f6658a519a:64, 0) | select(%1, 0:64, 0x6da5ad4ee619504c); \
                let %8 = %5 & 255; \
                let %9 = ~%6 ^ (%7 | %8 ^ %6); \
                let %10 = ~(%5 & (%7 ^ -256)); \
                let %11 = ~(%7 & 255) & ~%5; \
                ~(%9 * 0xaa9198db70383e98 + %10 * 0xaa9198db70383e98 + %11 * 0x556e67248fc7c168 & (%9 * 0xd2fe010764f7e887 + %10 * 0xd2fe010764f7e887 + %11 * 0x2d01fef89b081779 ^ (#6 & 255 | #12 & -256) + 0x4bc330b0be287ad4)) & (%4 + (~%4 & %7 & 255) | %3) * 0x556e67248fc7c169 + %10 * 0x556e67248fc7c169 - (%7 & %6 ^ (%8 | %7)) * 0x556e67248fc7c169";
    let cfg = ::bitwright::mba::MbaConfig::default();
    let (out, agrees) = with_mba(text, cfg.with_known_atoms(true));
    assert!(agrees, "{out}");
    assert_eq!(out, "0xaa9198db70383e97:64");
    assert_ne!(with_mba(text, cfg).0, "0xaa9198db70383e97:64");
}

#[test]
fn a_varying_noise_block_is_recovered_as_its_selector() {
    // One constant is computed per side of an event test, but each selected coefficient is
    // multiplied through complementary partitions of an unrelated word.
    let text = "let %0 = trunc<8>(q) == 0; \
                let %1 = select(%0, 0xe6229ed78bba3a02:64, 0x6917e97be2bd3a02); \
                let %2 = ~x; \
                let %3 = %2 & 0xfffffffebff828d3; \
                let %4 = select(%0, 0x8ceeb0943a22e2ff:64, 0xcb740b420ea162ff); \
                let %5 = ~%3 * %4; \
                let %6 = ~(%2 & 0x14007d72c) * %1; \
                let %7 = %3 * %4; \
                let %8 = ~(x & 0xfffffffebff828d3) * %4; \
                let %9 = %5 * 0xf03a49e91da5aae9; \
                ~(x & 0x14007d72c) * %1 * 0xf03a49e91da5aae9 \
                + select(%0, 0x3196701ba3cc70df:64, 0xb33d0377cd1af0df) \
                + %9 + %6 * 0xf03a49e91da5aae9 + %9 \
                + %7 * 0xf03a49e91da5aae9 + %8 * 0xf03a49e91da5aae9";
    let cfg = ::bitwright::mba::MbaConfig::default()
        .with_noise_forms(true)
        .with_known_atoms(true);
    let (out, agrees) = with_mba(text, cfg);
    assert!(agrees, "{out}");
    assert_eq!(
        out,
        "select(trunc<8>(q) == 0, 0x451e1d31ba270fe9:64, 0x32c85bd6d2048fe9)"
    );
}

#[test]
fn complementary_cofactors_cancel_even_when_the_products_are_shared() {
    let text = "let p = (rotl(y + 0xec502a030056cb7d, 51) + 0x416bf12db336dc49 \
                    | 0xbdbfffddef7fddbf) * 0x2cce5ea4d995f4d3; \
                let x = ~secret_input_zz & ~(b & 2); let u = p * x; let v = ~x * p; \
                select(z == 0, u + v, u * 7 + v * 7)";
    let (out, agrees) = noise_forms(text, true);
    assert!(agrees, "{out}");
    assert!(!out.contains("secret_input_zz"), "{out}");
}
