//! The sums of a question written one way ([`Config::shared_sums`]): the question written
//! again is the question asked, at every assignment; and a limb against its word's slice is
//! decided without a search to speak of.

use super::*;

/// Whether the two 1-bit expressions agree at every value of `#0:6` and `#1:6`.
fn same_everywhere(cx: &mut Context, a: Expr, b: Expr) -> Result<(), String> {
    for v in 0..1u64 << 12 {
        let env = crate::FnEnv(|k: &SymbolKey, w: Width| match k {
            SymbolKey::U64(0) => Some(BitVec::wrapping_from_u64(w, v & 63)),
            SymbolKey::U64(1) => Some(BitVec::wrapping_from_u64(w, v >> 6)),
            _ => None,
        });
        let r = cx.eval(&[a, b], &env).unwrap();
        if r[0] != r[1] {
            return Err(format!(
                "#0 = {}, #1 = {}: {} against {}",
                v & 63,
                v >> 6,
                r[0],
                r[1]
            ));
        }
    }
    Ok(())
}

/// A random 6-bit expression over `#0:6` and `#1:6`: sums, slices in every spelling, masks,
/// comparisons of low digits read as carries, and what a sum does not look through.
fn term(rng: &mut Rng, depth: u32) -> String {
    let pick = |rng: &mut Rng, n: u64| rng.next() % n;
    if depth == 0 {
        return match pick(rng, 5) {
            0 | 1 => "#0:6".into(),
            2 | 3 => "#1:6".into(),
            _ => format!("{}:6", pick(rng, 64)),
        };
    }
    let sub = |rng: &mut Rng| term(rng, depth - 1);
    let k = 1 + pick(rng, 5);
    match pick(rng, 22) {
        0 | 1 => format!("({} + {})", sub(rng), sub(rng)),
        2 | 3 => format!("({} - {})", sub(rng), sub(rng)),
        4 => format!("(0:6 - {})", sub(rng)),
        5 => format!("(~{})", sub(rng)),
        6 => format!("({} * {}:6)", sub(rng), pick(rng, 64)),
        7 => format!("({} << {k}:6)", sub(rng)),
        8 => format!("({} >>u {k}:6)", sub(rng)),
        9 => format!("({} & {}:6)", sub(rng), (1u64 << k) - 1),
        10 => format!(
            "({} & {}:6)",
            sub(rng),
            ((1u64 << k) - 1) << pick(rng, 6 - k + 1)
        ),
        11 => format!("zext<6>(trunc<{k}>({}))", sub(rng)),
        12 => format!("zext<6>(extract<{k}, {}>({}))", 6 - k, sub(rng)),
        13 => format!("sext<6>(trunc<{k}>({}))", sub(rng)),
        14 => format!(
            "concat(trunc<{}>({}), trunc<{k}>({}))",
            6 - k,
            sub(rng),
            sub(rng)
        ),
        15 => format!(
            "(({} << {k}:6) | ({} & {}:6))",
            sub(rng),
            sub(rng),
            (1u64 << k) - 1
        ),
        16 => format!(
            "zext<6>(trunc<{k}>({}) <u trunc<{k}>({}))",
            sub(rng),
            sub(rng)
        ),
        17 => format!(
            "sext<6>(({} & {m}:6) <u ({} & {m}:6))",
            sub(rng),
            sub(rng),
            m = (1u64 << k) - 1
        ),
        18 => format!("({} & {})", sub(rng), sub(rng)),
        19 => format!("({} ^ {})", sub(rng), sub(rng)),
        20 => format!(
            "trunc<6>(zext<12>({}) * zext<12>({}) >>u {k}:12)",
            sub(rng),
            sub(rng)
        ),
        _ => format!(
            "select({} <u {}, {}, {})",
            sub(rng),
            sub(rng),
            sub(rng),
            sub(rng)
        ),
    }
}

/// A handler's limb above bit `k` and its word's slice, at `w` bits over `#0` and `#1`: the
/// word is `steps` operands added and subtracted in turn, the limb their high digits with
/// the carry or the borrow of each step read off the low digits by a comparison.
fn limb(rng: &mut Rng, w: u16, k: u16, steps: usize) -> (String, String) {
    let j = w - k;
    let operand = |rng: &mut Rng| match rng.next() % 6 {
        0 => format!("#0:{w}"),
        1 => format!("#1:{w}"),
        2 => format!("(#0:{w} & #1:{w})"),
        3 => format!("((#0:{w} & #1:{w}) << 1:{w})"),
        4 => format!("(#1:{w} * {}:{w})", 3 + 2 * (rng.next() % 3)),
        _ => format!("{}:{w}", rng.next() % (1 << w)),
    };
    let lo = |e: &str| format!("trunc<{k}>({e})");
    let hi = |e: &str| format!("extract<{k}, {j}>({e})");
    let mut word = operand(rng);
    let mut high = hi(&word);
    for _ in 0..steps {
        let t = operand(rng);
        if rng.next().is_multiple_of(2) {
            let next = format!("({word} + {t})");
            high = format!(
                "({high} + {} + zext<{j}>({} <u {}))",
                hi(&t),
                lo(&next),
                lo(&t)
            );
            word = next;
        } else {
            let next = format!("({word} - {t})");
            high = format!(
                "({high} - {} - zext<{j}>({} <u {}))",
                hi(&t),
                lo(&word),
                lo(&next)
            );
            word = next;
        }
    }
    (high, hi(&word))
}

/// Soundness of [`sums::shared`]: the question written again equals the question asked at
/// every assignment, for random questions (true or not) and for limbs against their words.
#[test]
fn shared_sums_are_the_question_asked() {
    let mut rng = Rng(0x5eed_0001);
    let mut questions: Vec<(String, String, u16)> = Vec::new();
    for i in 0..220 {
        let depth = 1 + (i % 4) as u32;
        questions.push((term(&mut rng, depth), term(&mut rng, depth), 6));
    }
    for i in 0..80u64 {
        let (l, r) = limb(&mut rng, 6, 1 + (i % 5) as u16, 1 + (i % 3) as usize);
        questions.push((l, r, 6 - (1 + (i % 5) as u16)));
    }
    let cfg = Config::default()
        .with_simplify(false)
        .with_shared_sums(true);
    let mut constant = 0;
    for (i, (l, r, w)) in questions.into_iter().enumerate() {
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(w).unwrap());
        let (a, b) = (cx.parse(&l, &o).unwrap(), cx.parse(&r, &o).unwrap());
        let (ai, bi) = (cx.id(a).unwrap(), cx.id(b).unwrap());
        let asked = cx.c_cmp(crate::CmpOp::Eq, ai, bi).unwrap();
        let again = crate::prove::sums::shared(&mut cx, asked).unwrap();
        constant += usize::from(cx.is_const(again));
        let (asked, again) = (cx.handle(asked), cx.handle(again));
        if let Err(at) = same_everywhere(&mut cx, asked, again) {
            panic!("{l} == {r}\nwritten again: {}\nat {at}", cx.display(again));
        }
        // A limb is its word's slice, and the prover says so with the option.
        if i >= 220 {
            let out = equal(&mut cx, a, b, &cfg).unwrap();
            assert!(matches!(out, Outcome::Proved(_)), "{l} == {r}: {out:?}");
        }
    }
    // (Most of the limbs' questions come to the constant: nothing is left to search.)
    assert!(constant >= 40, "{constant}");
}

/// One handler's XOR limb at an 11/21 split over two free words, the carry and the borrow
/// read off the low limbs (the search alone takes 150,000 propagations to see through the
/// three-operand sum): with its sums written one way, the limb is its word's slice.
#[test]
fn a_limb_is_its_words_slice_with_shared_sums() {
    let word = "x:32 + y:32 - ((x & y) << 1)";
    for spelled in [
        "trunc<11>(x + y) <u trunc<11>(x)",
        "(x + y & 2047) <u (x & 2047)",
        "trunc<16>(x + y & 2047) <u trunc<16>(x & 2047)",
    ] {
        let limb = format!(
            "trunc<21>((x:32 >>u 11) + (y:32 >>u 11) - ((x & y) >>u 10) + zext<32>({spelled}) \
             - zext<32>(trunc<11>(x + y) <u trunc<11>({word})))"
        );
        let mut cx = Context::new();
        let o = ParseOptions::width(Width::new(21).unwrap());
        let a = cx.parse(&limb, &o).unwrap();
        let b = cx.parse(&format!("extract<11, 21>({word})"), &o).unwrap();
        let cfg = Config::default()
            .with_simplify(false)
            .with_shared_sums(true)
            .with_max_propagations(20_000);
        let out = equal(&mut cx, a, b, &cfg).unwrap();
        assert!(matches!(out, Outcome::Proved(_)), "{spelled}: {out:?}");
        // And a limb that is not its word's is refuted as before.
        let c = cx
            .parse(&format!("extract<11, 21>({word} + 2048)"), &o)
            .unwrap();
        let out = equal(&mut cx, a, c, &cfg).unwrap();
        assert!(matches!(out, Outcome::Refuted(_)), "{spelled}: {out:?}");
    }
}

/// A product by a constant in two limbs against the word's product: linear over the slices
/// of the operand, with one carry on each side.
#[test]
fn a_product_in_limbs_is_its_words_with_shared_sums() {
    let mut cx = Context::new();
    let o = ParseOptions::width(Width::new(20).unwrap());
    let a = cx
        .parse(
            "concat(extract<50, 13>(x:64 * 0x1224a8b3ecc0c29b), \
             extract<43, 7>((x >>u 25 & 0x1ffffff) * 0x1818536000000 \
             + (x & 0x1ffffff) * 0xa8b3ecc0c29b))",
            &o,
        )
        .unwrap();
    let b = cx
        .parse("extract<43, 20>(x:64 * 0x1224a8b3ecc0c29b)", &o)
        .unwrap();
    let cfg = Config::default()
        .with_simplify(false)
        .with_shared_sums(true)
        .with_max_propagations(20_000);
    let out = equal(&mut cx, a, b, &cfg).unwrap();
    assert!(matches!(out, Outcome::Proved(_)), "{out:?}");
}
