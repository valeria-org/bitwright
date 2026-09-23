//! The expression parser and printer: no panic on any text, and `parse(print(e)) == e`.
#![no_main]

use bitwright::{Context, ParseOptions, Width};
use libfuzzer_sys::fuzz_target;

fuzz_target!(|data: &[u8]| {
    let Some((&w, text)) = data.split_first() else {
        return;
    };
    let Ok(text) = std::str::from_utf8(text) else {
        return;
    };
    let width = Width::new(1 + u16::from(w) % 128).unwrap();
    let opts = ParseOptions::width(width);
    let mut cx = Context::new();
    let Ok(e) = cx.parse(text, &opts) else {
        return;
    };
    let printed = cx.display(e).to_string();
    let again = cx
        .parse(&printed, &opts)
        .unwrap_or_else(|err| panic!("the printer wrote unparsable text {printed:?}: {err}"));
    assert_eq!(again, e, "{text:?} printed as {printed:?}");
});
