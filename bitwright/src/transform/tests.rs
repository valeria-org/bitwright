//! Transformations with known answers: valid ones, and invalid ones with the counterexample
//! that shows why (poison, undefined behavior, NaNs, signed zeros, nondeterminism).

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
    let r = one(text);
    match r.verdict() {
        Verdict::Invalid(cx) => *cx,
        _ => panic!("expected invalid:\n{text}\n{r}"),
    }
}

fn input<'c>(cx: &'c Counterexample, name: &str) -> &'c Shown {
    &cx.inputs
        .iter()
        .find(|(n, ..)| n == name)
        .unwrap_or_else(|| panic!("{name}\n{cx}"))
        .2
}

#[test]
fn integer_peepholes() {
    valid(
        "%a = xor %x, -1
         %r = add %a, 1
           =>
         %r = sub 0, %x",
    );
    valid(
        "Pre: isPowerOf2(C)
         %r = mul %x, C
           =>
         %r = shl %x, log2(C)",
    );
    // With `nsw` an increment is larger (and overflow is poison, which anything refines);
    // but not at one bit, where 1 is −1.
    valid(
        "%a = add nsw i8 %x, 1
         %r = icmp sgt %a, %x
           =>
         %r = true",
    );
    let cx = invalid(
        "%a = add nsw %x, 1
         %r = icmp sgt %a, %x
           =>
         %r = true",
    );
    assert_eq!(cx.types, "i1");
    // Without it, it wraps.
    let cx = invalid(
        "%a = add %x, 1
         %r = icmp sgt %a, %x
           =>
         %r = true",
    );
    assert_eq!(cx.mismatch, Mismatch::Value);
    // Known bits: the mask keeps what the precondition says may be set.
    valid(
        "Pre: MaskedValueIsZero(%x, ~C)
         %r = and %x, C
           =>
         %r = %x",
    );
    // `x + x` is `x << 1`, except at one bit, where a shift by 1 is poison.
    let cx = invalid(
        "%r = add %x, %x
           =>
         %r = shl %x, 1",
    );
    assert_eq!(cx.types, "i1");
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    valid(
        "%r = add i8 %x, %x
           =>
         %r = shl i8 %x, 1",
    );
}

#[test]
fn poison_through_select() {
    // `select c, x, false` is not `c & x`: when c is false and x is poison, the select is
    // false and the and is poison.
    let cx = invalid(
        "%r = select %c, %x, false
           =>
         %r = and %c, %x",
    );
    assert_eq!(cx.mismatch, Mismatch::TargetPoison);
    assert_eq!(input(&cx, "%x"), &Shown::Poison);
    assert_eq!(
        input(&cx, "%c"),
        &Shown::Value(crate::BitVec::from_bool(false))
    );
    // Freezing x repairs it.
    valid(
        "%r = select %c, %x, false
           =>
         %f = freeze %x
         %r = and %c, %f",
    );
    // A frozen poison is some value, not poison: dropping the freeze is wrong.
    let cx = invalid(
        "%r = freeze %x
           =>
         %r = %x",
    );
    assert_eq!(input(&cx, "%x"), &Shown::Poison);
    // Adding one is fine.
    valid(
        "%r = %x
           =>
         %r = freeze %x",
    );
}

#[test]
fn undefined_behavior() {
    // PR20186 (the Alive paper): negating a quotient is not dividing by the negated divisor,
    // since INT_MIN / -1 is undefined.
    let cx = invalid(
        "%a = sdiv %X, C
         %r = sub 0, %a
           =>
         %r = sdiv %X, -C",
    );
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    // Removing a division that may be undefined is fine; adding one is not.
    valid(
        "%a = udiv %x, %y
         %r = mul %a, 0
           =>
         %r = 0",
    );
    let cx = invalid(
        "%r = mul %x, 0
           =>
         %a = udiv %x, %y
         %r = mul %a, 0",
    );
    assert_eq!(cx.mismatch, Mismatch::TargetUb);
    // A target may use a value of the source: it stays.
    valid(
        "%a = udiv i8 %x, %y
         %r = add %a, %a
           =>
         %r = shl %a, 1",
    );
}

#[test]
fn undef_and_choices() {
    // The source may pick undef as -1.
    valid(
        "%r = or %x, undef
           =>
         %r = -1",
    );
    // But `or x, undef` cannot be every value.
    invalid(
        "%r = or %x, undef
           =>
         %r = undef",
    );
    // A value from undef used twice in the target is refused.
    let r = one("%r = add %x, 1
           =>
         %u = and %x, undef
         %r = add %u, %u");
    assert!(matches!(r.verdict(), Verdict::Unsupported(_)), "{r}");
}

#[test]
fn floating_point() {
    // x + (−0) is x, NaNs included (a NaN result may keep its operand's payload and sign).
    valid(
        "%r = fadd %x, -0.0
           =>
         %r = %x",
    );
    // x + 0 is not: −0 + 0 is +0.
    let cx = invalid(
        "%r = fadd %x, 0.0
           =>
         %r = %x",
    );
    assert_eq!(cx.types, "half");
    valid(
        "%r = fadd nsz %x, 0.0
           =>
         %r = %x",
    );
    // x · 1 is x; the reverse is not, since a NaN result's sign is free.
    valid(
        "%r = fmul %x, 1.0
           =>
         %r = %x",
    );
    invalid(
        "%r = %x
           =>
         %r = fmul %x, 1.0",
    );
    // With nnan an ordered self-comparison is true (a NaN makes it poison).
    valid(
        "%r = fcmp nnan ord %x, %x
           =>
         %r = true",
    );
    invalid(
        "%r = fcmp ord %x, %x
           =>
         %r = true",
    );
}

/// The NaN rule the encoder states by operand classes is the arithmetic's: exhaustively in
/// tiny formats, for every operation it covers.
#[test]
fn nan_rules_match_the_arithmetic() {
    use super::encode::{Choices, Enc, Leaves, NanOp};
    use crate::fp::{FpFormat, FpTest, RoundingMode};
    use crate::{BitVec, Context, FnEnv, SymbolKey, Width};
    let t = super::ir::Transform::new("t".into());
    for f in [FpFormat::new(2, 3).unwrap(), FpFormat::new(3, 3).unwrap()] {
        let w = f.width();
        let mut cx = Context::new();
        let sym: Vec<_> = (0..3)
            .map(|k| cx.symbol(SymbolKey::U64(k), w).unwrap())
            .collect();
        let leaves = Leaves {
            inputs: Vec::new(),
            consts: Vec::new(),
        };
        let ops = [
            NanOp::Add,
            NanOp::Sub,
            NanOp::Mul,
            NanOp::Div,
            NanOp::Rem,
            NanOp::Sqrt,
            NanOp::Fma,
        ];
        let specs: Vec<_> = ops
            .iter()
            .map(|&op| {
                let arity = match op {
                    NanOp::Sqrt => 1,
                    NanOp::Fma => 3,
                    _ => 2,
                };
                let mut e = Enc::new(&mut cx, &t, &[], &leaves, Choices::Fixed(&[])).unwrap();
                e.nan_spec(op, f, &sym[..arity]).unwrap()
            })
            .collect();
        let n = 1u64 << w.bits();
        let rne = RoundingMode::Rne;
        for x in 0..n {
            for y in 0..n {
                let zs: &[u64] = &[0, 1, n / 2, n - 1, (n / 2) - 1, x ^ y];
                for &z in zs {
                    let v = |k: u64| BitVec::wrapping_from_u64(w, k);
                    let (a, b, c) = (v(x), v(y), v(z));
                    let env = FnEnv(|k: &SymbolKey, _| match k {
                        SymbolKey::U64(0) => Some(a),
                        SymbolKey::U64(1) => Some(b),
                        SymbolKey::U64(2) => Some(c),
                        _ => None,
                    });
                    let got = cx.eval(&specs, &env).unwrap();
                    let actual = [
                        f.add(rne, &a, &b).unwrap(),
                        f.sub(rne, &a, &b).unwrap(),
                        f.mul(rne, &a, &b).unwrap(),
                        f.div(rne, &a, &b).unwrap(),
                        f.rem(&a, &b).unwrap(),
                        f.sqrt(rne, &a).unwrap(),
                        f.fma(rne, &a, &b, &c).unwrap(),
                    ];
                    for (k, r) in actual.iter().enumerate() {
                        let nan = f.test(FpTest::Nan, r).unwrap();
                        assert_eq!(
                            !got[k].is_zero(),
                            nan,
                            "{:?} in {f:?} at {x:#x} {y:#x} {z:#x}",
                            ops[k]
                        );
                    }
                }
            }
        }
        let _ = Width::W1;
    }
}

fn tv(src: &str, tgt: &str) -> Vec<Report> {
    let pairs = pairs(src, Some(tgt)).unwrap_or_else(|e| panic!("{e}"));
    pairs
        .iter()
        .map(|t| verify(t, &Config::default()))
        .collect()
}

#[test]
fn translation_validation() {
    let src = "
define i8 @branches(i8 %x, i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  %y = add i8 %x, 1
  br label %m
b:
  %z = sub i8 %x, 1
  br label %m
m:
  %r = phi i8 [ %y, %a ], [ %z, %b ]
  ret i8 %r
}

define i8 @select(i8 %x, i1 %c) {
  %d = select i1 %c, i8 1, i8 -1
  %r = add i8 %x, %d
  ret i8 %r
}

define i32 @frozen(i32 noundef %x) {
  %f = freeze i32 %x
  %r = mul i32 %f, 8
  ret i32 %r
}

define i32 @switch(i32 %x) {
entry:
  switch i32 %x, label %d [
    i32 0, label %z
    i32 1, label %o
  ]
z:
  ret i32 10
o:
  ret i32 11
d:
  %r = add i32 %x, 10
  ret i32 %r
}

define i8 @ranged(i8 range(i8 0, 10) %x) {
  %r = urem i8 %x, 16
  ret i8 %r
}

define void @assume(i8 %x) {
  %c = icmp ult i8 %x, 10
  call void @llvm.assume(i1 %c)
  ret void
}
";
    let tgt = "
define i8 @branches(i8 %x, i1 %c) {
  %d = select i1 %c, i8 1, i8 -1
  %r = add i8 %x, %d
  ret i8 %r
}

define i8 @select(i8 %x, i1 %c) {
entry:
  br i1 %c, label %a, label %b
a:
  %y = add i8 %x, 1
  br label %m
b:
  %z = sub i8 %x, 1
  br label %m
m:
  %r = phi i8 [ %y, %a ], [ %z, %b ]
  ret i8 %r
}

define i32 @frozen(i32 noundef %x) {
  %r = shl i32 %x, 3
  ret i32 %r
}

define i32 @switch(i32 %x) {
  %r = add i32 %x, 10
  ret i32 %r
}

define i8 @ranged(i8 %x) {
  ret i8 %x
}

define void @assume(i8 %x) {
  %c = icmp ult i8 %x, 20
  call void @llvm.assume(i1 %c)
  ret void
}
";
    let reports = tv(src, tgt);
    let verdict = |name: &str| {
        let r = reports.iter().find(|r| r.name == name).unwrap();
        (r.verdict(), r.to_string())
    };
    // Branches that merge into a select: fine. The other way: a branch on poison is
    // undefined, a select on poison is not.
    assert!(
        matches!(verdict("branches").0, Verdict::Valid),
        "{}",
        verdict("branches").1
    );
    match verdict("select").0 {
        Verdict::Invalid(cx) => assert_eq!(cx.mismatch, Mismatch::TargetUb),
        v => panic!("{v:?}"),
    }
    // A noundef value needs no freeze.
    assert!(
        matches!(verdict("frozen").0, Verdict::Valid),
        "{}",
        verdict("frozen").1
    );
    // The switch's cases are the add.
    assert!(
        matches!(verdict("switch").0, Verdict::Valid),
        "{}",
        verdict("switch").1
    );
    // Within its range, x urem 16 is x.
    assert!(
        matches!(verdict("ranged").0, Verdict::Valid),
        "{}",
        verdict("ranged").1
    );
    // A weaker assumption is fine (the target has no undefined behavior the source lacks).
    assert!(
        matches!(verdict("assume").0, Verdict::Valid),
        "{}",
        verdict("assume").1
    );
    // A stronger one is not.
    let r = tv(
        "define void @f(i8 %x) {\n  ret void\n}\n",
        "define void @f(i8 %x) {\n  %c = icmp ult i8 %x, 20\n  call void @llvm.assume(i1 %c)\n  ret void\n}\n",
    );
    match r[0].verdict() {
        Verdict::Invalid(cx) => assert_eq!(cx.mismatch, Mismatch::TargetUb),
        v => panic!("{v:?}"),
    }
    // One file with @src and @tgt.
    let one = pairs(
        "define i8 @src(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n\
         define i8 @tgt(i8 %x) {\n  %r = add i8 %x, %x\n  ret i8 %r\n}\n",
        None,
    )
    .unwrap();
    assert!(matches!(
        verify(&one[0], &Config::default()).verdict(),
        Verdict::Valid
    ));
    // Loops are outside the subset.
    let looped = tv(
        "define i8 @f(i8 %x) {\nentry:\n  br label %l\nl:\n  br label %l\n}\n",
        "define i8 @f(i8 %x) {\n  ret i8 %x\n}\n",
    );
    assert!(
        matches!(looped[0].verdict(), Verdict::Unsupported(_)),
        "{}",
        looped[0]
    );
}

#[test]
fn syntax_errors_name_the_line() {
    let e = parse_transforms("%r = add %x\n=>\n%r = %x").unwrap_err();
    assert_eq!(e.line, 1);
    let tgt = "define i8 @tgt(i8 %x) {\n  ret i8 %x\n}\n";
    let e = pairs(
        &format!("define i8 @src(i8 %x) {{\n  ret i8 %x 1\n}}\n{tgt}"),
        None,
    )
    .unwrap_err();
    assert_eq!(e.line, 2);
    let e = pairs(
        &format!("define i8 @src(i8 %x) {{\n  %r = frob i8 %x\n  ret i8 %r\n}}\n{tgt}"),
        None,
    )
    .unwrap_err();
    assert!(e.message.contains("frob"), "{e}");
}

fn inferred(text: &str) -> Inference {
    let ts = parse_transforms(text).unwrap_or_else(|e| panic!("{e}"));
    infer(&ts[0], &Config::default()).unwrap_or_else(|e| panic!("{e}"))
}

#[test]
fn preconditions_are_inferred() {
    // A multiplication is a shift by a power of two.
    let i = inferred(
        "%r = mul %x, C
           =>
         %r = shl %x, log2(C)",
    );
    assert_eq!(i.pre.as_deref(), Some("isPowerOf2(C)"));
    assert!(i.weakest);
    assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
    // The mask keeps every bit the or does not set.
    let i = inferred(
        "%a = and %x, C1
         %r = or %a, C2
           =>
         %r = or %x, C2",
    );
    assert_eq!(i.pre.as_deref(), Some("(C1 | C2) == -1"));
    assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
    // Two shifts are one when the sum is in range, or when either is too far (then the
    // source is poison).
    let i = inferred(
        "%a = shl %x, C1
         %r = shl %a, C2
           =>
         %r = shl %x, C1 + C2",
    );
    let pre = i.pre.clone().unwrap();
    assert!(i.weakest, "{pre}");
    assert!(
        pre.contains("C1 + C2 u< width(C1)") && pre.contains("u>= width"),
        "{pre}"
    );
    assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
    // Valid as it is: no precondition.
    let i = inferred(
        "%r = add %x, C
           =>
         %r = sub %x, -C",
    );
    assert_eq!(i.pre, None);
    assert!(matches!(i.report.unwrap().verdict(), Verdict::Valid));
}
