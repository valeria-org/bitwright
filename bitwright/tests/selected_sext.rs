//! Recognizing the high half of a sign extension supplied by a conditional mask.

use bitwright::engine::{Engine, Phase, Strategy};
use bitwright::{Context, ParseOptions, Width};

fn casts() -> Engine {
    Engine::builder()
        .builtin()
        .strategy(Strategy::new("casts", vec![Phase::Casts]))
        .build()
        .unwrap()
}

#[test]
fn recognizes_sign_predicate_polarities_at_the_source_width() {
    let engine = casts();
    for (src, want) in [
        (
            "select(x:7 <u 64, 0:13, 8064) | zext<13>(x)",
            "sext<13>(x:7)",
        ),
        (
            "zext<13>(x:7) | select(x <=s -1, 8064:13, 0)",
            "sext<13>(x:7)",
        ),
        ("zext<8>(x:1) | select(x, 254:8, 0)", "sext<8>(x:1)"),
        (
            "select(extract<69, 1>(x:70), -1:137 << 70, 0) | zext<137>(x)",
            "sext<137>(x:70)",
        ),
        // The neighbouring arithmetic spelling must not form `(1u64 << 64) - 1`.
        (
            "((x:128 & 0xffffffffffffffff) ^ 0x8000000000000000) - 0x8000000000000000",
            "sext<128>(trunc<64>(x:128))",
        ),
    ] {
        let mut cx = Context::new();
        let opts = ParseOptions::width(Width::W64);
        let input = cx.parse(src, &opts).unwrap();
        let expected = cx.parse(want, &opts).unwrap();
        let got = engine.simplify(&mut cx, input).unwrap().expr;
        assert_eq!(got, expected, "{src} gave {}", cx.display(got));
    }
}

#[test]
fn rejects_nearby_conditions_and_masks() {
    let engine = casts();
    for selection in [
        "select(9 <=u x, 0xf0:8, 0)",
        "select(8 <u x, 0xf0:8, 0)",
        "select(8 <=u y:4, 0xf0:8, 0)",
        "select(x <s 0, 0:8, 0xf0)",
        "select(extract<2, 1>(x), 0xf0:8, 0)",
        "select(8 <=u x, 0xe0:8, 0)",
        "select(8 <=u x, 0xf1:8, 0)",
        "select(8 <=u x, 0xf0:8, 1)",
    ] {
        let mut cx = Context::new();
        let opts = ParseOptions::width(Width::W8);
        let input = cx
            .parse(&format!("zext<8>(x:4) | {selection}"), &opts)
            .unwrap();
        let got = engine.simplify(&mut cx, input).unwrap().expr;
        assert_eq!(got, input, "{selection} gave {}", cx.display(got));
    }
}

#[cfg(all(feature = "mba", feature = "prove"))]
#[test]
fn proves_both_minimal_residues_independently_of_the_simplifier() {
    use bitwright::engine::Sharing;
    use bitwright::mba::MbaConfig;
    use bitwright::prove::{self, Config, Outcome};

    let strategy = Strategy::deobfuscate()
        .with_mba(MbaConfig::default())
        .with_sharing(Sharing::Ignored)
        .with_max_region(1024);
    let engine = Engine::builder()
        .builtin()
        .strategy(strategy)
        .build()
        .unwrap();
    let sign = "zext<64>($1:32) | select(0x80000000 <=u $1, 0xffffffff00000000:64, 0)";
    let difference = format!("({sign}) - sext<64>($1)");
    let cfg = Config::default()
        .with_simplify(false)
        .with_samples(0)
        .with_certificate(true);
    for (src, want) in [(sign, "sext<64>($1:32)"), (difference.as_str(), "0:64")] {
        let mut cx = Context::new();
        let opts = ParseOptions::width(Width::W64);
        let input = cx.parse(src, &opts).unwrap();
        let expected = cx.parse(want, &opts).unwrap();
        let got = engine.simplify(&mut cx, input).unwrap().expr;
        assert_eq!(got, expected, "{src} gave {}", cx.display(got));
        let Outcome::Proved(Some(cert)) = prove::equal(&mut cx, input, expected, &cfg).unwrap()
        else {
            panic!("no certificate for {src} = {want}");
        };
        cert.check().unwrap();
    }
}
