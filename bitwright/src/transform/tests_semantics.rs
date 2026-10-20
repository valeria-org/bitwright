//! Each program's own attributes, call sites, `nsz`, what is refused rather than ignored,
//! type assignments, redefined registers, malformed functions, labels and metadata as LLVM
//! writes them, and the certified and exported questions.

use super::*;

fn one(text: &str) -> Report {
    let ts = parse_transforms(text).unwrap_or_else(|e| panic!("{e}\n{text}"));
    assert_eq!(ts.len(), 1, "{text}");
    verify(&ts[0], &Config::default())
}

fn valid(text: &str) {
    let r = one(text);
    assert!(
        matches!(r.verdict(), Verdict::Valid),
        "expected valid:\n{text}\n{r}"
    );
}

fn invalid(text: &str) -> Counterexample {
    invalid_report(&one(text))
}

fn invalid_report(r: &Report) -> Counterexample {
    match r.verdict() {
        Verdict::Invalid(cx) => *cx,
        v => panic!("expected invalid, got {v:?}\n{r}"),
    }
}

fn unsupported(r: &Report) -> String {
    match r.verdict() {
        Verdict::Unsupported(why) => why,
        v => panic!("expected unsupported, got {v:?}\n{r}"),
    }
}

fn input<'c>(cx: &'c Counterexample, name: &str) -> &'c Shown {
    &cx.inputs
        .iter()
        .find(|(n, ..)| n == name)
        .unwrap_or_else(|| panic!("{name}\n{cx}"))
        .2
}

fn tv1(src: &str, tgt: &str) -> Report {
    let ts = pairs(src, Some(tgt)).unwrap_or_else(|e| panic!("{e}"));
    assert_eq!(ts.len(), 1);
    verify(&ts[0], &Config::default())
}

const IDENTITY: &str = "define i8 @f(i8 %x) {\n  ret i8 %x\n}\n";

#[test]
fn each_program_reads_its_inputs_through_its_own_attributes() {
    // A target that adds `noundef` to a parameter has undefined behavior where a caller
    // passes poison, which the source allows.
    let cx = invalid_report(&tv1(
        IDENTITY,
        "define i8 @f(i8 noundef %x) {\n  ret i8 %x\n}\n",
    ));
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    assert_eq!(*input(&cx, "%x"), Shown::Poison);
    // One that adds `range` makes an argument out of it poison.
    let cx = invalid_report(&tv1(
        IDENTITY,
        "define i8 @f(i8 range(i8 0, 10) %x) {\n  ret i8 %x\n}\n",
    ));
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    // And `nofpclass(nan)`, a NaN.
    let cx = invalid_report(&tv1(
        "define float @f(float %x) {\n  ret float %x\n}\n",
        "define float @f(float nofpclass(nan) %x) {\n  ret float %x\n}\n",
    ));
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    // The same attributes on both: fine.
    let same = "define i8 @f(i8 noundef range(i8 0, 10) %x) {\n  ret i8 %x\n}\n";
    assert!(matches!(tv1(same, same).verdict(), Verdict::Valid));
    // The source's attributes are its own. With `noundef` and `range`, an argument out of
    // the range is the source's undefined behavior, so the target may do anything there; a
    // target without the range sees the argument as it is, never poison.
    let r = tv1(
        same,
        "define i8 @f(i8 noundef %x) {\n  %r = and i8 %x, 15\n  ret i8 %r\n}\n",
    );
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    // An unused parameter's `noundef` is undefined behavior at the call all the same.
    let cx = invalid_report(&tv1(
        "define i8 @f(i8 %x, i8 %y) {\n  ret i8 %x\n}\n",
        "define i8 @f(i8 %x, i8 noundef %y) {\n  ret i8 %x\n}\n",
    ));
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    assert_eq!(*input(&cx, "%y"), Shown::Poison);
    // `returned` (which clang infers): callers may rely on it, so returning another value
    // is undefined behavior.
    let two = "define i8 @f(i8 %x, i8 %y) {\n  ret i8 %x\n}\n";
    let r = tv1(
        two,
        "define i8 @f(i8 returned %x, i8 %y) {\n  ret i8 %x\n}\n",
    );
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    let cx = invalid_report(&tv1(
        two,
        "define i8 @f(i8 %x, i8 returned %y) {\n  ret i8 %x\n}\n",
    ));
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    // The argument is what it returns, even where its return range makes the result poison.
    let r = tv1(
        "define range(i8 0, 10) i8 @f(i8 %x, i8 %y) {
  ret i8 %x
}
",
        "define range(i8 0, 10) i8 @f(i8 returned %x, i8 %y) {
  ret i8 %x
}
",
    );
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    // An attribute the target adds that bitwright does not model is not ignored.
    let why = unsupported(&tv1(
        two,
        "define i8 @f(i8 \"acme-hint\"=\"7\" %x, i8 %y) {\n  ret i8 %x\n}\n",
    ));
    assert!(why.contains("acme-hint"), "{why}");
    // ABI attributes change nothing.
    let r = tv1(IDENTITY, "define i8 @f(i8 signext %x) {\n  ret i8 %x\n}\n");
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
}

#[test]
fn undef_in_functions_is_refused_where_its_uses_could_differ() {
    let zero = "define i8 @f(i8 %x) {\n  ret i8 0\n}\n";
    // `%u` may differ at each use: `sub %u, %u` may be anything.
    let why = unsupported(&tv1(
        zero,
        "define i8 @f(i8 %x) {\n  %u = add i8 undef, 0\n  %r = sub i8 %u, %u\n  ret i8 %r\n}\n",
    ));
    assert!(why.contains("%u depends on undef"), "{why}");
    // Through a register whose definition comes later in the text (block order is free).
    let why = unsupported(&tv1(
        zero,
        "define i8 @f(i8 %x) {\nentry:\n  br label %b\nm:\n  %v = add i8 %u, 0\n  \
         %r = sub i8 %v, %v\n  ret i8 %r\nb:\n  %u = add i8 undef, 0\n  br label %m\n}\n",
    ));
    assert!(why.contains("%v depends on undef"), "{why}");
    // A branch on it.
    let why = unsupported(&tv1(
        zero,
        "define i8 @f(i8 %x) {\nentry:\n  %c = icmp eq i8 undef, 0\n  \
         br i1 %c, label %a, label %b\na:\n  ret i8 0\nb:\n  ret i8 0\n}\n",
    ));
    assert!(why.contains("branch"), "{why}");
    // Frozen, it is one value.
    let r = tv1(
        zero,
        "define i8 @f(i8 %x) {\n  %u = freeze i8 undef\n  %r = sub i8 %u, %u\n  ret i8 %r\n}\n",
    );
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
}

#[test]
fn pointers_and_memory_are_refused() {
    for (src, tgt) in [
        (
            "define ptr @f(ptr %p, ptr %q) {\n  %c = icmp eq ptr %p, %q\n  \
             %r = select i1 %c, ptr %p, ptr %q\n  ret ptr %r\n}\n",
            "define ptr @f(ptr %p, ptr %q) {\n  ret ptr %q\n}\n",
        ),
        (
            "define i64 @f(i64 %p, i64 %i) {\n  %q = getelementptr i8, ptr null, i64 %i\n  \
             %r = ptrtoint ptr %q to i64\n  ret i64 %r\n}\n",
            "define i64 @f(i64 %p, i64 %i) {\n  ret i64 %i\n}\n",
        ),
    ] {
        let why = unsupported(&tv1(src, tgt));
        assert!(why.contains("pointers"), "{why}");
    }
    // In the transformation syntax too.
    let r = one("%a = inttoptr i64 %x to ptr\n%r = ptrtoint ptr %a to i64\n=>\n%r = %x");
    assert!(matches!(r.verdict(), Verdict::Unsupported(_)), "{r}");
}

#[test]
fn call_site_attributes_are_modeled() {
    let umin = |args: &str, ret: &str| {
        format!(
            "define i8 @f(i8 %x, i8 %y) {{\n  %r = call {ret}i8 @llvm.umin.i8({args})\n  \
             ret i8 %r\n}}\n"
        )
    };
    let src = umin("i8 %x, i8 %y", "");
    // A poison `noundef` argument is undefined behavior.
    let cx = invalid_report(&tv1(&src, &umin("i8 noundef %x, i8 %y", "")));
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    // So is a poison `noundef` result.
    let cx = invalid_report(&tv1(&src, &umin("i8 %x, i8 %y", "noundef ")));
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    // A result range that holds is fine (what clang writes on a population count) ...
    let pop = |ret: &str| {
        format!(
            "define i32 @f(i32 %x) {{\n  %r = tail call {ret}i32 @llvm.ctpop.i32(i32 %x)\n  \
             ret i32 %r\n}}\n"
        )
    };
    let r = tv1(&pop(""), &pop("range(i32 0, 33) "));
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    // ... and one too narrow makes poison.
    let cx = invalid_report(&tv1(&pop(""), &pop("range(i32 0, 32) ")));
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    // nofpclass on a result.
    let fabs = |ret: &str| {
        format!(
            "define float @f(float %x) {{\n  %r = call {ret}float @llvm.fabs.f32(float %x)\n  \
             ret float %r\n}}\n"
        )
    };
    let cx = invalid_report(&tv1(&fabs(""), &fabs("nofpclass(nan) ")));
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    // Metadata that may change a result is not modeled, so not ignored either; debug
    // information is harmless.
    let fdiv = |md: &str| {
        format!(
            "define float @f(float %x, float %y) {{\n  %r = fdiv float %x, %y{md}\n  \
             ret float %r\n}}\n"
        )
    };
    let why = unsupported(&tv1(&fdiv(""), &fdiv(", !fpmath !0")));
    assert!(why.contains("!fpmath"), "{why}");
    let r = tv1(&fdiv(""), &fdiv(", !dbg !7"));
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    // In the source, an unmodeled annotation only makes it more defined than it is.
    let r = tv1(&fdiv(", !fpmath !0"), &fdiv(""));
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
}

#[test]
fn nsz_frees_the_sign_of_a_zero_result() {
    // 1.0 + -1.0 is +0.0, which `nsz` lets be -0.0: adding the flag is not a refinement.
    for (src, tgt) in [
        ("%r = fadd float %x, -1.0", "%r = fadd nsz float %x, -1.0"),
        (
            "%r = call float @llvm.fabs.f32(float %x)",
            "%r = call nsz float @llvm.fabs.f32(float %x)",
        ),
        (
            "%r = call float @llvm.maxnum.f32(float %x, float 0.0)",
            "%r = call nsz float @llvm.maxnum.f32(float %x, float 0.0)",
        ),
        (
            "%r = call float @llvm.fma.f32(float %x, float 2.0, float -2.0)",
            "%r = call nsz float @llvm.fma.f32(float %x, float 2.0, float -2.0)",
        ),
    ] {
        let cx = invalid(&format!("{src}\n=>\n{tgt}"));
        assert_eq!(cx.mismatch, Mismatch::Value, "{src}");
    }
    // Removing the flag is fine; and with it, a zero result may lose its sign.
    valid("%r = fadd nsz float %x, -1.0\n=>\n%r = fadd float %x, -1.0");
    valid("%a = fsub nsz float %x, 1.0\n%r = fneg nsz %a\n=>\n%r = fsub nsz float 1.0, %x");
}

#[test]
fn fast_math_flags_make_a_select_floating_point() {
    // Untyped, the flag says the values are floating point: a NaN result is now poison.
    let cx = invalid("%r = select %c, %x, %y\n=>\n%r = select nnan %c, %x, %y");
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    // Without flags, a select stays generic (checked over integers).
    valid("%r = select %c, %x, %y\n=>\n%n = xor %c, true\n%r = select %n, %y, %x");
}

#[test]
fn every_type_assignment_is_checked_or_the_verdict_is_unknown() {
    // Two related open types: all 55 assignments, up to i32 into i64.
    let r = one("%a = zext %x\n%r = trunc %a\n=>\n%r = %x");
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
    assert_eq!(r.checks.len(), 55);
    assert!(r.checks.iter().any(|(l, _)| l == "%a: i64, %x: i32"), "{r}");
    assert_eq!(r.unchecked, 0);
    // Three independent ones, more than the most checked: not valid, unknown.
    let text = "%a = icmp eq %x, 0\n%b = icmp eq %y, 0\n%c = icmp eq %z, 0\n\
                %t = and %a, %b\n%r = and %t, %c\n=>\n%u = and %b, %c\n%r = and %a, %u";
    let ts = parse_transforms(text).unwrap();
    let small = Config::default().with_widths(vec![1, 2, 3, 4, 5, 6]);
    let r = verify(&ts[0], &small.clone().with_max_types(100));
    match r.verdict() {
        Verdict::Unknown(why) => {
            assert!(why.contains("100 type assignments checked of 216"), "{why}");
        }
        v => panic!("{v:?}"),
    }
    assert_eq!(r.unchecked, 116);
    // With room for all of them, valid.
    let r = verify(&ts[0], &small.with_max_types(216));
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
}

#[test]
fn redefined_registers_are_refined_too() {
    // The target defines %a again: the rewrite replaces it at its other uses, so it must
    // refine the source's %a, whatever the root does with it.
    let cx = invalid("%a = add %x, 1\n%r = and %a, 0\n=>\n%a = add %x, 2\n%r = 0");
    assert_eq!(cx.output.as_deref(), Some("%a"));
    assert!(cx.to_string().contains("the values of %a differ"), "{cx}");
    // Defined again alike: valid.
    valid("%a = add %x, 1\n%r = mul %a, 2\n=>\n%a = sub %x, -1\n%r = shl %a, 1");
    // The target's %a may be more defined than the source's.
    valid("%a = add nsw %x, 1\n%r = mul %a, 2\n=>\n%a = add %x, 1\n%r = shl %a, 1");
}

#[test]
fn malformed_functions_are_syntax_errors() {
    let err = |body: &str| -> SyntaxError {
        let src = format!("define i8 @src(i8 %x, i1 %c) {{\n{body}}}\n");
        let both = format!("{src}define i8 @tgt(i8 %x, i1 %c) {{\n  ret i8 %x\n}}\n");
        pairs(&both, None).unwrap_err()
    };
    // An empty block is not `unreachable`.
    let e = err("entry:\n  br i1 %c, label %a, label %b\na:\nb:\n  ret i8 %x\n");
    assert!(e.message.contains("block %a has no terminator"), "{e}");
    assert_eq!(e.line, 4);
    // A value that reads itself, or one read before it is defined.
    let e = err("  %y = add i8 %y, 1\n  ret i8 %y\n");
    assert!(e.message.contains("its own definition"), "{e}");
    let e = err("  %y = add i8 %z, 1\n  %z = add i8 %y, 1\n  ret i8 %z\n");
    assert!(e.message.contains("does not dominate"), "{e}");
    // A value defined on one path, read after the paths join.
    let e = err(
        "entry:\n  br i1 %c, label %a, label %b\na:\n  %y = add i8 %x, 1\n  br label %b\n\
         b:\n  ret i8 %y\n",
    );
    assert!(e.message.contains("%y does not dominate"), "{e}");
    // A phi without an entry for one of its block's edges.
    let e = err(
        "entry:\n  br i1 %c, label %a, label %m\na:\n  br label %m\nm:\n  \
         %r = phi i8 [ 1, %a ]\n  ret i8 %r\n",
    );
    assert!(e.message.contains("one entry for each edge"), "{e}");
    // A block named twice.
    let e = err("a:\n  br label %a\na:\n  ret i8 %x\n");
    assert!(e.message.contains("defined twice"), "{e}");
}

/// A diamond on `%c` whose blocks `a`, `b` and `m` are spelled as given, each as its label and
/// as its uses, with `md` after the phi.
fn diamond([(a, ua), (b, ub), (m, um)]: [(&str, &str); 3], md: &str) -> String {
    format!(
        "define i8 @f(i8 %x, i1 %c) {{\nentry:\n  br i1 %c, label %{ua}, label %{ub}\n\
         {a}:\n  %y = add i8 %x, 1\n  br label %{um}\n{b}:\n  %z = sub i8 %x, 1\n  \
         br label %{um}\n{m}:\n  %r = phi i8 [ %y, %{ua} ], [ %z, %{ub} ]{md}\n  ret i8 %r\n}}\n"
    )
}

#[test]
fn labels_are_read_as_llvm_spells_them() {
    let plain = diamond([("a", "a"), ("b", "b"), ("m", "m")], "");
    for blocks in [
        // As optimizations name blocks.
        [
            (".lr.ph", ".lr.ph"),
            ("._crit_edge", "._crit_edge"),
            (".loopexit", ".loopexit"),
        ],
        [
            ("if-then", "if-then"),
            ("if-else", "if-else"),
            ("if-end", "if-end"),
        ],
        // Quoted where the name needs it and where it does not: the same block either way.
        [
            ("\"if then\"", "\"if then\""),
            ("\"b\"", "b"),
            ("m", "\"m\""),
        ],
        [("0", "0"), ("1", "1"), ("2", "2")],
        [("$a", "$a"), ("-1", "-1"), ("1b", "\"1b\"")],
        // A quoted name may hold a bracket, which must not open a statement over lines.
        [("\"a[b\"", "\"a[b\""), ("b", "b"), ("m", "m")],
    ] {
        // The same function: each phi entry and branch is read from its own block.
        let r = tv1(&plain, &diamond(blocks, ""));
        assert!(matches!(r.verdict(), Verdict::Valid), "{blocks:?}\n{r}");
    }
}

#[test]
fn metadata_after_a_phi_is_metadata() {
    let blocks = [("a", "a"), ("b", "b"), ("m", "m")];
    let plain = diamond(blocks, "");
    for md in [", !dbg !7", ", !annotation !0, !dbg !7"] {
        let r = tv1(&plain, &diamond(blocks, md));
        assert!(matches!(r.verdict(), Verdict::Valid), "{md}\n{r}");
    }
    // Metadata bitwright does not know is not ignored.
    let why = unsupported(&tv1(&plain, &diamond(blocks, ", !acme !0")));
    assert!(why.contains("!acme"), "{why}");
}

#[test]
fn debug_records_are_skipped() {
    let plain = diamond([("a", "a"), ("b", "b"), ("m", "m")], "");
    // The diamond as `clang -g` writes it: debug records from LLVM 19 on, calls of the
    // `llvm.dbg` intrinsics before.
    let records: [fn(&str) -> String; 3] = [
        |v| format!("    #dbg_value(i8 {v}, !12, !DIExpression(), !11)\n    #dbg_label(!13, !11)"),
        |v| {
            format!(
                "  call void @llvm.dbg.value(metadata i8 {v}, metadata !12, \
                 metadata !DIExpression()), !dbg !11\n  call void @llvm.dbg.label(metadata !13)"
            )
        },
        |v| {
            format!(
                "  tail call void @llvm.dbg.value(metadata i8 {v}, metadata !12, metadata !DIExpression(DW_OP_LLVM_fragment, 0, 8)), !dbg !11"
            )
        },
    ];
    for record in records {
        let f = format!(
            "define i8 @f(i8 %x, i1 %c) !dbg !5 {{\nentry:\n{}\n  \
             br i1 %c, label %a, label %b, !dbg !11\na:\n  %y = add i8 %x, 1, !dbg !11\n{}\n  \
             br label %m, !dbg !11\nb:\n  %z = sub i8 %x, 1, !dbg !11\n  br label %m\nm:\n  \
             %r = phi i8 [ %y, %a ], [ %z, %b ], !dbg !11\n{}\n  ret i8 %r, !dbg !11\n}}\n",
            record("%x"),
            record("%y"),
            record("%r"),
        );
        let r = tv1(&plain, &f);
        assert!(matches!(r.verdict(), Verdict::Valid), "{f}\n{r}");
    }
    // Records of every kind before the first instruction of a block without a label.
    let r = tv1(
        "define i8 @f(i8 %x) {\n  %y = add i8 %x, 1\n  ret i8 %y\n}\n",
        "define i8 @f(i8 %x) !dbg !5 {\n    #dbg_declare(ptr undef, !12, !DIExpression(), !11)\n    \
         #dbg_assign(i8 %x, !12, !DIExpression(), !14, ptr undef, !DIExpression(), !11)\n  \
         notail call void @llvm.dbg.label(metadata !13) #3\n  %y = add i8 %x, 1, !dbg !11\n  \
         ret i8 %y, !dbg !11\n}\n",
    );
    assert!(matches!(r.verdict(), Verdict::Valid), "{r}");
}

#[test]
fn validation_goes_on_past_a_function_outside_the_subset() {
    let src = "define i8 @a(i8 %x) {\n  ret i8 %x\n}\n\ndefine i8 @b(i8 %x) {\n  ret i8 %x\n}\n";
    let tgt = "define i8 @a(i8 %x) {\n  %y = frob i8 %x\n  ret i8 %y\n}\n\n\
               define i8 @b(i8 %x) {\n  %y = or i8 %x, 0\n  ret i8 %y\n}\n";
    let reports = validate(src, Some(tgt), &Config::default()).unwrap();
    assert_eq!(reports.len(), 2);
    assert!(unsupported(&reports[0]).contains("frob"));
    assert!(matches!(reports[1].verdict(), Verdict::Valid));
    // `pairs` stays strict.
    assert!(pairs(src, Some(tgt)).is_err());
}

#[test]
fn floating_point_environments_are_refused() {
    let f = |attrs: &str| {
        format!(
            "define float @f(float %x) {attrs} {{\n  %r = fadd float %x, -0.0\n  \
             ret float %r\n}}\n"
        )
    };
    let plain = f("");
    for (attrs, tail) in [
        ("strictfp", ""),
        (
            "#0",
            "attributes #0 = { nounwind \"denormal-fp-math\"=\"preserve-sign,preserve-sign\" }\n",
        ),
    ] {
        let tgt = format!("{}{tail}", f(attrs));
        let why = unsupported(&tv1(&plain, &tgt));
        assert!(
            why.contains("strictfp") || why.contains("denormal"),
            "{why}"
        );
    }
    // A relaxation the target declares is refused; the default environment is fine.
    let tgt = format!(
        "{}attributes #0 = {{ \"no-signed-zeros-fp-math\"=\"true\" }}\n",
        f("#0")
    );
    assert!(unsupported(&tv1(&plain, &tgt)).contains("no-signed-zeros"));
    let tgt = format!(
        "{}attributes #0 = {{ nounwind \"denormal-fp-math\"=\"ieee,ieee\" }}\n",
        f("#0")
    );
    assert!(matches!(tv1(&plain, &tgt).verdict(), Verdict::Valid));
    // An integer function does not care.
    let i = "define i8 @f(i8 %x) strictfp {\n  ret i8 %x\n}\n";
    assert!(matches!(tv1(i, i).verdict(), Verdict::Valid));
}

#[test]
fn preconditions_may_name_the_sources_registers() {
    // The precondition is about %a, the source's register, not a fresh input of that name.
    valid(
        "Pre: MaskedValueIsZero(%a, 1)
         %a = mul %x, %y
         %r = and %a, 1
           =>
         %r = 0",
    );
}

#[test]
fn inference_with_constants_of_independent_types() {
    // C1 and C2 never share a type: no atom relates them, and examples at different widths
    // are no trouble.
    let ts = parse_transforms(
        "%a = shl %x, C1
         %c1 = icmp eq %a, 0
         %c2 = icmp ult %y, C2
         %d = icmp ne %y, 3
         %e = and %c2, %d
         %r = or %c1, %e
           =>
         %c0 = icmp eq %x, 0
         %r = or %c0, %e",
    )
    .unwrap();
    let i = infer(&ts[0], &Config::default()).unwrap();
    let pre = i.pre.unwrap();
    assert!(!pre.contains("C2"), "{pre}");
    assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
}

#[test]
fn certified_verdicts_agree() {
    let cfg = Config::default()
        .with_certify(true)
        .with_widths(vec![1, 2, 4, 8]);
    for (text, expect_valid) in [
        ("%a = xor %x, -1\n%r = add %a, 1\n=>\n%r = sub 0, %x", true),
        ("%r = select %c, %x, false\n=>\n%r = and %c, %x", false),
        ("%r = fadd half %x, -0.0\n=>\n%r = %x", true),
    ] {
        let ts = parse_transforms(text).unwrap();
        let r = verify(&ts[0], &cfg);
        match r.verdict() {
            Verdict::Valid => assert!(expect_valid, "{r}"),
            Verdict::Invalid(_) => assert!(!expect_valid, "{r}"),
            v => panic!("{v:?}\n{r}"),
        }
    }
}

#[cfg(feature = "smtlib")]
#[test]
fn final_questions_as_smtlib() {
    let ts = parse_transforms("%a = xor i8 %x, -1\n%r = add %a, 1\n=>\n%r = sub 0, %x").unwrap();
    let qs = smt(&ts[0], &Config::default()).unwrap();
    assert_eq!(qs.len(), 1);
    let (label, script) = &qs[0];
    let script = script.as_ref().unwrap();
    assert!(label.contains("transformation 1"), "{label}");
    assert!(script.contains("expect unsat") && script.ends_with("(check-sat)\n"));
    // The script's question is the one bitwright answered: read back, it has no model.
    let mut cx = crate::Context::new();
    let imported = crate::smtlib::import(&mut cx, script).unwrap();
    let root = imported.definition("root0").unwrap();
    let not = cx.un(crate::UnOp::Not, root).unwrap();
    assert!(matches!(
        crate::prove::valid(&mut cx, not, &Default::default()).unwrap(),
        crate::prove::Outcome::Proved(_)
    ));
}
