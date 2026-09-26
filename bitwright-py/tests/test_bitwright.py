"""Tests of the Python bindings: `pip install ./bitwright-py pytest && pytest bitwright-py/tests`."""

import struct
import threading

import pytest

import bitwright as bw


@pytest.fixture
def cx():
    return bw.Context()


def test_the_readme_examples(cx):
    engine = bw.Engine.standard()
    for text, simplified in [
        ("(x & y) + (x | y)", "x + y"),
        ("((x ^ 0x5a) + 3 - 3) ^ 0x5a", "x"),
        ("x * 0x87c37b91114253d5 == y * 0x87c37b91114253d5", "x == y"),
        (
            "let m = (x ^ 0xd3220fb78e33751f) * 0xd3220fb78e33751f; "
            "(m ^ ((m >>u 32) >>u (m >>u 60))) * 0xd3220fb78e33751f == 0",
            "x == 0xd3220fb78e33751f",
        ),
    ]:
        assert str(engine.simplify(cx.parse(text, 64))) == simplified


def test_simplify_like_the_command_line():
    # A nonlinear MBA: the deobfuscation engine's MBA service solves it, the standard one not.
    mba = "(x & y) * (x | y) + (x & ~y) * (~x & y)"
    assert bw.simplify(mba) == "x * y"
    assert bw.simplify(mba, deobfuscate=False) != "x * y"
    assert bw.simplify("x & 0xffff0000", 32, assume=["x <u 0x10000"]) == "0:32"
    assert bw.simplify("x + 1", 8) == "x + 1"


def test_operators_build_canonical_expressions(cx):
    x, y = cx.symbols("x y", 32)
    assert y + x == x + y  # hash-consing: one node
    assert hash(y + x) == hash(x + y)
    assert len({x + y, y + x, x}) == 2
    assert str(x + 1) == "x + 1"
    assert str(1 + x) == "x + 1"
    assert str(5 - x) == "5 - x"
    assert str(~x & 0xFF) == "~x & 255"
    assert str(x >> 3) == "x >>u 3"
    assert str(x.ashr(3)) == "x >>s 3"
    assert str(x // y) == "udiv(x, y)"
    assert str(x % 7) == "urem(x, 7)"
    assert str(-x) == "-x"
    assert str(x.ult(y)) == "x <u y"
    assert str(x.sge(0)) == "0 <=s x"  # stored as a swapped `sle`
    assert str(x.extract(8, 8).zext(32)) == "zext<32>(extract<8, 8>(x))"
    assert x.concat(y).width == 64
    assert x.bit(3).width == 1
    c = x.eq(y)
    assert str(c.select(x, 0)) == "select(x == y, x, 0)"
    # An int too wide for the other operand's width.
    with pytest.raises(ValueError):
        x + 2**32
    assert (x + (-1)).eval(x=0) == 2**32 - 1
    with pytest.raises(ValueError):
        x + (-(2**31) - 1)
    # Floats are not operands.
    with pytest.raises(TypeError):
        x + 1.5


def test_equality_is_identity_and_truth_is_explicit(cx):
    x = cx.symbol("x", 8)
    assert x == cx.symbol("x", 8)
    assert x != cx.symbol("y", 8)
    assert x != 3
    other = bw.Context()
    assert x != other.symbol("x", 8)
    with pytest.raises(TypeError):
        bool(x.eq(1))
    with pytest.raises(TypeError):
        if x.ult(3):
            pass


def test_inspection(cx):
    x, y = cx.symbols("x y", 16)
    e = (x + y) * 3
    assert e.kind == "binary" and e.op == "mul"
    assert e.children == [x + y, cx.const(3, 16)]
    assert e.children[1].kind == "const" and e.children[1].value == 3
    assert x.kind == "symbol" and x.name == "x" and x.op is None and x.value is None
    assert x.ugt(y).kind == "compare"
    assert x.ugt(y).op == "ult"  # stored with the operands swapped
    assert x.ugt(y).children == [y, x]
    assert x.extract(4, 8).lo == 4
    assert x.popcnt().op == "popcnt"
    assert cx.const(-2, 16).value == 0xFFFE
    assert cx.const(-2, 16).signed_value == -2
    assert cx.symbol(7, 8).name == "#7"
    assert cx.fresh_symbol(8).name.startswith("$")
    assert cx.parse("let t = x + 1; t * t").dag_size() == 4
    assert e.context is cx
    assert repr(x + y) == "<bitwright.Expr 16: x + y>"
    t = cx.parse("let t = x * y; t + (t >>u 3)")
    assert t.to_string().startswith("let")
    assert t.to_string(lets=False, symbol_widths=True) == "x:16 * y:16 + (x * y >>u 3)"


def test_wide_values(cx):
    w = cx.symbol("w", 300)
    big = 2**299 + 12345
    assert (w ^ big).eval(w=big) == 0
    assert (w + 1).eval(w=2**300 - 1) == 0
    assert cx.const(big, 300).value == big
    assert cx.const(-(2**299), 300).signed_value == -(2**299)
    assert cx.const(-1, 300).value == 2**300 - 1
    with pytest.raises(ValueError):
        cx.const(2**300, 300)
    with pytest.raises(ValueError):
        cx.const(-(2**299) - 1, 300)
    f = (w & (2**300 - 2)).facts()
    assert f.known_zero == 1 and f.umax == 2**300 - 2


def test_eval_and_substitute(cx):
    x, y = cx.symbols("x y", 8)
    e = x * 3 + y
    assert e.eval(x=100, y=1) == 45
    assert e.eval({x: 100, "y": 1}) == 45
    with pytest.raises(bw.BitwrightError, match="y"):
        e.eval(x=1)
    with pytest.raises(ValueError):
        e.eval(x=256, y=0)
    assert str(e.substitute({x: y + 1, y: 5})) == "(y + 1) * 3 + 5"
    with pytest.raises(TypeError):
        e.substitute({"x": 1})


def test_errors(cx):
    x = cx.symbol("x", 8)
    with pytest.raises(bw.ParseError, match="expected an expression"):
        cx.parse("x +")
    with pytest.raises(bw.ParseError):
        cx.parse("p + q")  # no width to infer
    with pytest.raises(bw.WidthError):
        x + cx.symbol("y", 16)
    with pytest.raises(bw.WidthError):
        cx.symbol("x", 16)
    with pytest.raises(bw.WidthError):
        cx.symbol("z", 0)
    with pytest.raises(bw.WidthError):
        x.zext(4)
    with pytest.raises(bw.BitwrightError, match="different context"):
        x + bw.Context().symbol("x", 8)
    cx.clear()
    assert len(cx) == 0
    with pytest.raises(bw.BitwrightError, match="cleared"):
        x + 1
    assert issubclass(bw.WidthError, bw.BitwrightError)
    small = bw.Context(max_nodes=4)
    with pytest.raises(bw.BitwrightError, match="full"):
        small.parse("a + b + c + d", 8)


def test_facts_proofs_and_assumptions(cx):
    b = cx.symbol("b", 8)
    f = ((b & 0xF0) | 1).facts()
    assert (f.known_zero, f.known_one, f.umin, f.umax) == (0x0E, 0x01, 1, 0xF1)
    assert f.ustride == 16  # 1, 17, 33, ..., 241: the low four bits are known
    assert f.smin < 0 and f.constant is None and f.relies_on == ()
    assert "known zero 0xe" in repr(f) and "[1, 241] by 16" in repr(f)
    assert cx.const(5, 8).facts().ustride == 0
    a = bw.Assumptions()
    assert a.assume(b.ult(16)) == 0
    assert len(a) == 1
    masked = (b & 0xF0).eq(0)
    assert masked.prove() is None
    assert masked.prove(a) is True
    assert b.uge(16).prove(a) is False
    fa = b.facts(a)
    assert fa.umax == 15 and fa.relies_on == (0,)
    assert (b & 0).eq(0).prove() is True
    with pytest.raises(bw.WidthError):
        a.assume(b)
    a.assume(b.ult(16), holds=False)
    assert a.infeasible
    with pytest.raises(bw.BitwrightError, match="contradict"):
        b.facts(a)
    # Invertibility.
    h = (b ^ 0x5A) * 0x1D
    assert h.prove_injective(b, bijective=True) is True
    assert (b & 0x0F).prove_injective(b) is not True


def test_engines_budgets_and_outcomes(cx):
    x = cx.symbol("x", 32)
    y = cx.symbol("y", 32)
    engine = bw.Engine()
    a = bw.Assumptions(x.ult(0x10000))
    out = engine.run([(x & y) + (x | y), x & 0xFFFF0000, x], assumptions=a)
    assert [str(o.expr) for o in out] == ["x + y", "0:32", "x"]
    assert [o.changed for o in out] == [True, True, False]
    assert [o.end for o in out] == ["completed"] * 3
    assert [o.relies_on for o in out] == [(), (0,), ()]
    stopped = engine.run([cx.parse("(p & q) + (p | q)", 32)], budget=bw.Budget(node_visits=0))
    assert stopped[0].end == "budget" and stopped[0].limit == "node visits"
    assert engine.run([]) == []
    b = bw.Budget(mba_calls=None, rewrites=10)
    assert b.mba_calls is None and b.rewrites == 10 and b.node_visits == 1 << 22
    assert bw.Budget.unlimited().node_visits is None
    with pytest.raises(TypeError):
        bw.Budget(node_vists=1)  # type: ignore[call-arg]
    with pytest.raises(ValueError):
        bw.Engine("fast")  # type: ignore[arg-type]
    assert repr(bw.Engine.deobfuscate()) == "<bitwright.Engine deobfuscate>"
    mba = (x & y) * (x | y) + (x & ~y) * (~x & y)
    assert str(mba.simplify(bw.Engine.deobfuscate())) == "x * y"
    assert str(mba.simplify()) != "x * y"
    # Each expression on its own, on threads: as a call with that one alone.
    exprs = [(x & y) + (x | y), x & 0xFFFF0000, x, mba, (x & y) + (x | y)]
    deob = bw.Engine.deobfuscate()
    for threads in (1, 4, 0):
        each = deob.run_each(exprs, threads=threads, assumptions=a)
        assert [str(o.expr) for o in each] == ["x + y", "0:32", "x", "x * y", "x + y"]
        assert [o.relies_on for o in each] == [(), (0,), (), (), ()]
    assert deob.run_each([]) == []


RULES = """bitwright 1;
group my.rules {
    rule and_or_complement<W>(x: W, y: W) { (x | y) & (x | ~y) => x }
}"""


def test_rules_of_your_own(cx):
    e = cx.parse("(a | b) & (a | ~b)", 64)
    ledger = bw.check_rules(RULES)
    assert ledger.startswith("#")
    choices: list[list[str | tuple[str, str | None]]] = [[RULES], [(RULES, ledger)], [(RULES, None)]]
    for rules in choices:
        engine = bw.Engine(rules=rules, max_rounds=2)
        assert str(engine.simplify(e)) == "a"
    with pytest.raises(bw.RuleError, match="unsound"):
        bw.check_rules("bitwright 1;\ngroup g {\n    rule bad<W>(x: W, y: W) { x | y => x }\n}")
    with pytest.raises(bw.RuleError):
        bw.Engine(rules=["nonsense"])
    with pytest.raises(bw.RuleError):
        bw.Engine(rules=[(RULES, "junk")])
    other = bw.check_rules("bitwright 1;\ngroup g {\n    rule r<W>(x: W) { x ^ x => 0 }\n}")
    with pytest.raises(bw.RuleError):
        bw.Engine(rules=[(RULES, other)])


def test_smtlib_round_trip(cx):
    e = cx.parse("udiv(x, y) + (x << 3)", 8)
    script = cx.to_smtlib(e)
    assert "(define-fun root0 () (_ BitVec 8)" in script
    other = bw.Context()
    imp = other.from_smtlib(script + "(assert (= root0 #x00))\n")
    assert set(imp.symbols) == {"x", "y"}
    assert str(imp.definitions["root0"]) == str(e)
    assert len(imp.assertions) == 1 and imp.assertions[0].width == 1
    with pytest.raises(bw.ParseError):
        other.from_smtlib("(assert")


def test_python_code_run_by_an_operation_may_use_the_context(cx):
    # Converting arguments can run Python code (`__index__`, an int subclass's `to_bytes`); no
    # lock is held then, so that code may use the same context.
    w = cx.symbol("w", 300)

    class Wide(int):
        def to_bytes(self, *args, **kwargs):  # type: ignore[override]
            cx.symbol("inner", 8)
            return int(self).to_bytes(*args, **kwargs)

    class Key:
        def __index__(self) -> int:
            cx.symbol("other", 8)
            return 7

    assert w.eval(w=Wide(2**299)) == 2**299
    assert (w ^ Wide(2**299)).eval(w=0) == 2**299
    assert cx.symbol(Key(), 8).name == "#7"
    o = cx.symbol("o", 256)
    assert o.fadd(Wide(2**255), bw.F256).fmul(o, bw.F256).width == 256


# ----- floating point ----------------------------------------------------------------------------


def f16(v: float) -> int:
    """The binary16 encoding of `v`."""
    return int(struct.unpack("<H", struct.pack("<e", v))[0])


def f32(v: float) -> int:
    """The binary32 encoding of `v`."""
    return int(struct.unpack("<I", struct.pack("<f", v))[0])


def f64(v: float) -> int:
    """The binary64 encoding of `v`."""
    return int(struct.unpack("<Q", struct.pack("<d", v))[0])


def test_float_formats():
    assert bw.FpFormat(8, 24) == bw.F32 and bw.F32 != bw.F64 and bw.F32 != (8, 24)
    assert hash(bw.FpFormat(8, 24)) == hash(bw.F32)
    assert len({bw.F16, bw.BF16, bw.FpFormat(5, 11)}) == 2
    assert repr(bw.F32) == "FpFormat(8, 24)"
    named = [
        (bw.F16, "f16", 5, 11),
        (bw.BF16, "bf16", 8, 8),
        (bw.F32, "f32", 8, 24),
        (bw.F64, "f64", 11, 53),
        (bw.F128, "f128", 15, 113),
        (bw.F256, "f256", 19, 237),
        (bw.X87, None, 15, 64),
    ]
    for f, name, eb, sb in named:
        assert (f.name, f.eb, f.sb, f.width) == (name, eb, sb, eb + sb)
    assert bw.FpFormat(3, 4).name is None and bw.FpFormat(2, 510).width == 512
    for eb, sb in [(1, 8), (32, 8), (8, 1), (11, 502), (8, 2**32 - 1)]:
        with pytest.raises(bw.WidthError, match="floating-point format"):
            bw.FpFormat(eb, sb)


def test_float_operations_are_the_text_syntax(cx):
    a, b, c = cx.symbols("a b c", 32)
    d, i, x = cx.symbol("d", 64), cx.symbol("i", 16), cx.symbol("x", 80)
    tiny = bw.FpFormat(3, 4)
    cases = [
        (a.fadd(b, bw.F32), "fp.add.rne.f32(a, b)"),
        (a.fsub(b, bw.F32, "rtz"), "fp.sub.rtz.f32(a, b)"),
        (a.fmul(b, bw.F32, rm="rtp"), "fp.mul.rtp.f32(a, b)"),
        (a.fdiv(b, bw.F32, "rtn"), "fp.div.rtn.f32(a, b)"),
        (a.ffma(b, c, bw.F32, "rna"), "fp.fma.rna.f32(a, b, c)"),
        (a.fsqrt(bw.F32), "fp.sqrt.rne.f32(a)"),
        (a.frem(b, bw.F32), "fp.rem.f32(a, b)"),
        (a.fround(bw.F32, "rtz"), "fp.round.rtz.f32(a)"),
        (a.fmin(b, bw.F32), "fp.min.f32(a, b)"),
        (a.fmax(b, bw.F32), "fp.max.f32(a, b)"),
        (a.feq(b, bw.F32), "fp.eq.f32(a, b)"),
        (a.flt(b, bw.F32), "fp.lt.f32(a, b)"),
        (a.fle(b, bw.F32), "fp.le.f32(a, b)"),
        (a.fgt(b, bw.F32), "fp.gt.f32(a, b)"),
        (a.fge(b, bw.F32), "fp.ge.f32(a, b)"),
        (a.fneg(bw.F32), "fp.neg.f32(a)"),
        (a.fabs(bw.F32), "fp.abs.f32(a)"),
        (a.fcopysign(b, bw.F32), "fp.copysign.f32(a, b)"),
        (a.fisnan(bw.F32), "fp.isnan.f32(a)"),
        (a.fisinf(bw.F32), "fp.isinf.f32(a)"),
        (a.fiszero(bw.F32), "fp.iszero.f32(a)"),
        (a.fissubnormal(bw.F32), "fp.issubnormal.f32(a)"),
        (a.fisnormal(bw.F32), "fp.isnormal.f32(a)"),
        (a.fisneg(bw.F32), "fp.isneg.f32(a)"),
        (a.fispos(bw.F32), "fp.ispos.f32(a)"),
        (a.fconvert(bw.F64, bw.F32), "fp.convert.rne.f32.f64(a)"),
        (d.fconvert(tiny, bw.F64, "rtz"), "fp.convert.rtz<11, 53, 3, 4>(d)"),
        (i.to_float(bw.F64), "fp.from_sbv.rne.f64(i)"),
        (i.to_float(bw.F16, "rtp", signed=False), "fp.from_ubv.rtp.f16(i)"),
        (d.to_int(32, bw.F64, "rtz"), "fp.to_sbv.rtz.f64<32>(d)"),
        (d.to_int(8, bw.F64, signed=False), "fp.to_ubv.rne.f64<8>(d)"),
        (x.x87_load(), "fp.x87_load(x)"),
        (x.x87_load().x87_store(), "fp.x87_store(fp.x87_load(x))"),
    ]
    for e, text in cases:
        assert e == cx.parse(text), text
    assert str(a.fadd(b, bw.F32, "rtz")) == "fp.add.rtz.f32(a, b)"
    assert str(d.to_int(32, bw.F64, "rtz")) == "fp.to_sbv.rtz.f64<32>(d)"
    # The sign operations and the tests are bit-vector operators.
    assert str(a.fneg(bw.F32)) == "a ^ 0x80000000"
    assert str(a.fabs(bw.F32)) == "a & 0x7fffffff"
    # An int operand is an encoding: a constant of the width.
    assert str(a.fmul(0x40400000, bw.F32)) == "fp.mul.rne.f32(a, 0x40400000)"


def test_float_evaluation(cx):
    a, b = cx.symbols("a b", 32)
    near, down = a.fadd(b, bw.F32), a.fadd(b, bw.F32, "rtz")
    # 0.1 + 0.2 in binary32: the exact sum lies 3/4 of the way to the next value up, so to
    # nearest it rounds up (to 0.3f), toward zero one unit in the last place lower.
    assert near.eval(a=f32(0.1), b=f32(0.2)) == f32(0.3) == 0x3E99999A
    assert down.eval(a=f32(0.1), b=f32(0.2)) == f32(0.3) - 1
    # Operations on constants fold, exactly.
    tenth = cx.const(f32(0.1), 32)
    fifth = tenth.fadd(tenth, bw.F32)
    assert fifth.kind == "const" and fifth.value == f32(0.2)
    # A NaN result is the canonical NaN, equal to nothing.
    d = cx.symbol("d", 64)
    root = d.fsqrt(bw.F64)
    assert root.eval(d=f64(-1.0)) == 0x7FF8000000000000
    assert root.feq(root, bw.F64).eval(d=f64(-1.0)) == 0
    assert root.feq(root, bw.F64).eval(d=f64(4.0)) == 1
    # Conversions to integers saturate, and a NaN converts to 0.
    to_i32 = d.to_int(32, bw.F64, "rtz")
    assert to_i32.eval(d=f64(1e10)) == 0x7FFFFFFF
    assert to_i32.eval(d=f64(-2.9)) == 2**32 - 2
    assert to_i32.eval(d=f64(float("nan"))) == 0
    # binary16 has 11 bits of precision: 2049 rounds to 2048, or up to 2050.
    i = cx.symbol("i", 16)
    assert i.to_float(bw.F16, signed=False).eval(i=2049) == f16(2048.0)
    assert i.to_float(bw.F16, "rtp", signed=False).eval(i=2049) == f16(2050.0)
    # Any format: binary64 widens to binary128 exactly, and back.
    wide = d.fconvert(bw.F128, bw.F64)
    assert wide.eval(d=f64(0.1)) == 0x3FFB999999999999A000000000000000
    assert wide.fconvert(bw.F64, bw.F128).eval(d=f64(0.1)) == f64(0.1)
    # x87: a load and a store give an encoding back; an unnormal loads as the NaN.
    x = cx.symbol("x", 80)
    one = 0x3FFF << 64 | 1 << 63
    assert x.x87_load().x87_store().eval(x=one) == one
    assert x.x87_load().eval(x=0x3FFF << 64) == 0x3FFFC000000000000000


def test_float_inspection(cx):
    a, b = cx.symbols("a b", 32)
    e = a.fmul(b, bw.F32, "rtz")
    assert (e.kind, e.op, e.format, e.rounding, e.to_format) == ("fp", "mul", bw.F32, "rtz", None)
    assert e.children == [a, b] and e.width == 32 and e.lo is None
    gt = a.fgt(b, bw.F32)
    assert (gt.kind, gt.op, gt.rounding, gt.width) == ("fp", "lt", None, 1)
    assert gt.children == [b, a]  # stored as `lt` with the operands swapped
    cv = a.fconvert(bw.F16, bw.F32, "rna")
    assert (cv.op, cv.format, cv.to_format, cv.rounding, cv.width) == (
        "convert",
        bw.F32,
        bw.F16,
        "rna",
        16,
    )
    i = cx.symbol("i", 16)
    fl = i.to_float(bw.F64, signed=False)
    assert (fl.op, fl.format, fl.children, fl.width) == ("from_ubv", bw.F64, [i], 64)
    to = a.to_int(8, bw.F32, "rtz")
    assert (to.op, to.format, to.rounding, to.width) == ("to_sbv", bw.F32, "rtz", 8)
    ops = [
        a.fadd(b, bw.F32),
        a.fmul(b, bw.F32),
        a.fdiv(b, bw.F32),
        a.ffma(b, b, bw.F32),
        a.fsqrt(bw.F32),
        a.frem(b, bw.F32),
        a.fround(bw.F32),
        a.fmin(b, bw.F32),
        a.fmax(b, bw.F32),
        a.feq(b, bw.F32),
        a.flt(b, bw.F32),
        a.fle(b, bw.F32),
        a.fconvert(bw.F64, bw.F32),
        i.to_float(bw.F32),
        i.to_float(bw.F32, signed=False),
        a.to_int(8, bw.F32),
        a.to_int(8, bw.F32, signed=False),
    ]
    names = "add mul div fma sqrt rem round min max eq lt le convert from_sbv from_ubv to_sbv to_ubv"
    assert [e.op for e in ops] == names.split()
    assert all(e.kind == "fp" for e in ops)
    assert [e.rounding is None for e in ops[5:12]] == [True, False, True, True, True, True, True]
    # Operations built from bit-vector operators, and other nodes, have no format.
    assert a.fneg(bw.F32).kind == "binary" and a.fneg(bw.F32).format is None
    assert a.fisnan(bw.F32).kind == "compare" and a.fisnan(bw.F32).rounding is None
    assert (a.format, a.to_format, a.rounding) == (None, None, None)


def test_float_facts_and_proofs(cx):
    i, j = cx.symbols("i j", 16)
    product = i.to_float(bw.F64).fmul(j.to_float(bw.F64), bw.F64)
    # An integer converted to a float is never a NaN, nor a product of two of them.
    assert product.fisnan(bw.F64).prove() is False
    assert str(product.fisnan(bw.F64).simplify()) == "0:1"
    # A byte converted to a float and back to 16 bits is below 256.
    b = cx.symbol("b", 8)
    back = b.to_float(bw.F64, signed=False).to_int(16, bw.F64, "rtz", signed=False)
    assert back.facts().umax == 255
    # The square root of a value known to be +0 to +inf is not a NaN.
    x = cx.symbol("x", 32)
    positive = bw.Assumptions(x.ule(0x7F800000))
    isnan = x.fsqrt(bw.F32).fisnan(bw.F32)
    assert isnan.prove() is None
    assert isnan.prove(positive) is False
    out = bw.Engine().run([isnan], assumptions=positive)[0]
    assert str(out.expr) == "0:1" and out.relies_on == (0,)


def test_float_smtlib_round_trip(cx):
    a, b = cx.symbols("a b", 32)
    e = a.fadd(b, bw.F32, "rtz").fmul(a, bw.F32)
    script = cx.to_smtlib(e)
    assert "(fp.add RTZ ((_ to_fp 8 24)" in script
    back = bw.Context().from_smtlib(script).definitions["root0"]
    assert str(back) == str(e) == "fp.mul.rne.f32(fp.add.rtz.f32(a, b), a)"


def test_float_errors(cx):
    a, h = cx.symbol("a", 32), cx.symbol("h", 16)
    with pytest.raises(bw.WidthError, match="widths differ"):
        a.fadd(h, bw.F32)
    with pytest.raises(bw.WidthError):
        a.fadd(a, bw.F64)
    with pytest.raises(bw.WidthError):
        h.fneg(bw.F32)
    with pytest.raises(bw.WidthError):
        h.fisnan(bw.F32)
    with pytest.raises(bw.WidthError):
        a.fconvert(bw.F64, bw.F16)
    with pytest.raises(bw.WidthError):
        a.x87_load()
    with pytest.raises(bw.WidthError):
        a.to_int(0, bw.F32)
    with pytest.raises(ValueError, match="rounding mode"):
        a.fadd(a, bw.F32, "up")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        a.fadd(a, "f32")  # type: ignore[arg-type]
    with pytest.raises(TypeError):
        a.fadd(1.5, bw.F32)  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        a.fadd(2**32, bw.F32)


def test_threads_share_engines_and_contexts():
    engine = bw.Engine.standard()
    shared = bw.Context()
    results = {}

    def work(i):
        own = bw.Context()
        x = own.symbol("x", 32)
        results[i] = str(engine.simplify((x & i) + (x | i)))
        s = shared.symbol("s", 32)
        engine.simplify((s & i) + (s | i))

    threads = [threading.Thread(target=work, args=(i,)) for i in range(1, 9)]
    for t in threads:
        t.start()
    for t in threads:
        t.join()
    assert results == {i: f"x + {i}" for i in range(1, 9)}


def test_proofs_synthesis_and_saturation(cx):
    x, y = cx.symbols("x y", 32)
    assert ((x ^ y) + 2 * (x & y)).equivalent(x + y) is True
    cex = (x + y).equivalent(x | y)
    assert isinstance(cex, dict) and set(cex) <= {"x", "y"}
    vx, vy = cex.get("x", 0), cex.get("y", 0)
    assert (vx + vy) % 2**32 != vx | vy
    assert bw.equivalent(x * 2, x + x) is True
    s = (((x + y) & 1) ^ (x & 1)).synthesize()
    assert s is not None and str(s) == "y & 1"
    assert (x + y).synthesize() is None
    z = cx.symbol("z", 32)
    f = (x * y + x * z).saturate()
    assert f is not None and str(f) == "(y + z) * x"


def test_engine_hooks(cx):
    x = cx.symbol("x", 8)
    e = x * 3 - x - x
    out, steps = bw.Engine().trace(e)
    assert str(out) == "x"
    assert steps and all(isinstance(by, str) for by, _, _ in steps)
    assert steps[-1][2] == out
    # Refusing the linear pass leaves the sum as the other passes and rules leave it.
    kept = bw.Engine(refuse=["linear"]).simplify(e)
    assert "linear" not in [by for by, _, _ in bw.Engine(refuse=["linear"]).trace(e)[1]]
    assert kept.equivalent(e) is True


def test_memory(cx):
    sp, x = cx.symbols("sp x", 64)
    m = bw.Memory(cx)
    slot = sp - 8
    m.store(slot, x)
    assert m.load(slot, 8) == x
    other = m.load(sp, 1)
    assert str(other) == "mem.0"
    assert len(m.reads()) == 1
    t = bw.Memory(cx, "t")
    t.set_bytes(0x1000, bytes([7, 8, 9]))
    assert t.load(cx.const(0x1001, 64)).value == 8


def test_lifting(cx):
    b = bw.lift_vex(
        cx,
        """t0 = GET:I64(rdi)
           t1 = GET:I64(rsi)
           t2 = Xor64(t0,t1)
           t3 = And64(t0,t1)
           t4 = Shl64(t3,0x01)
           t5 = Add64(t2,t4)
           PUT(rax) = t5""",
    )
    rax = b.register("rax")
    assert rax is not None and str(rax.simplify()) == "rdi + rsi"
    p = bw.lift_pcode(cx, "(register, RAX, 8) = INT_MULT (register, RDI, 8) , (const, 0x2, 8)")
    rax = p.register("RAX")
    assert rax is not None and str(rax.simplify()) == "RDI + RDI"
    ll = bw.lift_llvm(cx, "define i32 @f(i32 %a) {\n  %r = shl i32 %a, 1\n  ret i32 %r\n}\n")
    ret = ll.register("ret")
    assert ret is not None and str(ret.simplify()) == "a + a"


def test_transformations():
    reports = bw.verify_transforms(
        """Name: good
        %a = xor %x, -1
        %r = add %a, 1
          =>
        %r = sub 0, %x

        Name: bad
        %r = select %c, %x, false
          =>
        %r = and %c, %x"""
    )
    assert [r.verdict for r in reports] == ["valid", "invalid"]
    assert "poison" in reports[1].text
    tv = bw.validate_functions(
        "define i8 @src(i8 %x) {\n  %r = mul i8 %x, 2\n  ret i8 %r\n}\n"
        "define i8 @tgt(i8 %x) {\n  %r = add i8 %x, %x\n  ret i8 %r\n}\n"
    )
    assert tv[0].verdict == "valid"
    (i,) = bw.infer_preconditions("%r = mul %x, C\n  =>\n%r = shl %x, log2(C)")
    assert i.pre == "isPowerOf2(C)" and i.weakest and i.verdict == "valid"


def test_the_compile_preset_and_engine_options(cx):
    x, y = cx.symbols("x y", 32)
    e = (x ^ y) + 2 * (x & y)
    engine = bw.Engine.compile()
    assert repr(engine) == "<bitwright.Engine compile>"
    assert str(e.simplify(engine)) == "x + y"
    out, stats = engine.run([e], stats=True)
    assert str(out[0].expr) == "x + y"
    assert stats.rounds == 1 and stats.memo_hits > 0  # answered by the memo
    assert isinstance(stats.passes, dict) and stats.host.calls == 0
    assert "visits" in repr(stats)
    each, stats = engine.run_each([e, x], threads=2, stats=True)
    assert [str(o.expr) for o in each] == ["x + y", "x"] and stats.node_visits >= 0
    # The options on another preset.
    tuned = bw.Engine("standard", sharing="ignored", max_region=16)
    assert str(e.simplify(tuned)) == "x + y"
    assert str(bw.Engine("compile", sharing="roots").simplify(e)) == "x + y"
    with pytest.raises(ValueError):
        bw.Engine(sharing="some")  # type: ignore[arg-type]
    with pytest.raises(ValueError):
        bw.Engine("fastest")  # type: ignore[arg-type]


def test_declared_known_bits(cx):
    x = cx.symbol("x", 8)
    assert cx.declared_known(x) is None
    cx.declare_known(x, (0xF0, 0))
    assert cx.declared_known(x) == (0xF0, 0)
    assert (x >> 4).prove() is False  # zero: never nonzero
    assert str((x >> 4).simplify(bw.Engine.compile())) == "0:8"
    assert x.facts().umax == 15
    cx.declare_known(x, (0, 0))
    assert cx.declared_known(x) is None
    wide = cx.symbol("w", 200)
    cx.declare_known(wide, (1 << 199, 1))
    assert cx.declared_known(wide) == (1 << 199, 1)
    assert wide.facts().umin == 1
    with pytest.raises(ValueError):
        cx.declare_known(x, (1, 1))  # a bit both 0 and 1
    with pytest.raises(ValueError):
        cx.declare_known(x, (0x100, 0))  # wider than the symbol
    with pytest.raises(TypeError):
        cx.declare_known(x + 1, (1, 0))
    with pytest.raises(TypeError):
        cx.declared_known(x + 1)
    n = len(cx)
    cx.reserve(1 << 16)
    assert len(cx) == n


def needless_rem(site, e):
    """`urem(x, c)` as `x` when the facts show `x < c`."""
    if site.op(e) != "urem":
        return None
    x, c = site.children(e)
    bound, facts = site.value(c), site.facts(x)
    if bound is None or facts is None or facts.umax >= bound:
        return None
    return x


def test_host_rewrites(cx):
    b = cx.symbol("b", 8)
    e = b.zext(32).urem(1000)
    rw = bw.Rewrite("acme.needless_rem", needless_rem, group="acme", revision=2)
    assert (rw.name, rw.group, rw.revision) == ("acme.needless_rem", "acme", 2)
    assert "acme.needless_rem" in repr(rw)
    # The built-in rules and passes leave it.
    assert e.simplify(bw.Engine.compile()) == e
    for engine in (
        bw.Engine("compile", rewrites=[rw]),
        bw.Engine("compile", trusted_rewrites=[rw]),
    ):
        out, stats = engine.run([e], stats=True)
        assert str(out[0].expr) == "zext<32>(b)"
        assert stats.host.changed == 1 and stats.host.calls >= 1
    # On threads, each expression on its own.
    exprs = [(b.zext(32) + k).urem(300) for k in range(1, 9)]
    each, stats = bw.Engine(trusted_rewrites=[rw]).run_each(exprs, threads=4, stats=True)
    assert [str(o.expr) for o in each] == [f"zext<32>(b) + {k}" for k in range(1, 9)]
    assert stats.host.changed == 8
    # Refused by name.
    refused = bw.Engine("compile", trusted_rewrites=[rw], refuse=["acme.needless_rem"])
    out, stats = refused.run([e], stats=True)
    assert out[0].expr == e and stats.hook_vetoes > 0

    # A wrong rewrite, sampled: rejected and quarantined.
    x, y, z = cx.symbols("x y z", 16)
    drop_addend = bw.Rewrite("acme.drop", lambda s, n: s.children(n)[0] if s.op(n) == "add" else None)
    out, stats = bw.Engine("compile", rewrites=[drop_addend]).run([x * y + z], stats=True)
    assert str(out[0].expr) == "x * y + z"
    assert stats.quarantined >= 1 and stats.host.rejected >= 1


def test_the_site(cx, monkeypatch):
    b = cx.symbol("b", 8)
    e = b.zext(32).urem(7)
    seen = []

    def inspect(site, n):
        if site.op(n) != "urem":
            return None
        x, c = site.children(n)
        seen.append(site)
        assert site.kind(n) == "binary" and site.kind(x) == "zext" and site.kind(c) == "const"
        assert site.width(n) == 32 and site.width(0) is None and site.kind(0) is None
        assert site.value(c) == 7 and site.value(x) is None
        assert site.to_string(n) == "urem(zext<32>(b), 7)"
        assert site.lo(site.extract(x, 2, 4)) == 2 and site.lo(x) is None
        assert site.children(0) == []
        facts = site.facts(x)
        assert facts.umax == 255 and facts.relies_on == ()
        one = site.constant(1, 32)
        minus = site.constant(-1, 32)
        assert site.value(minus) == 0xFFFFFFFF
        built = [
            site.un("neg", x),
            site.bin("add", x, one),
            site.cmp("ult", x, one),
            site.zext(x, 64),
            site.sext(x, 64),
            site.trunc(x, 8),
            site.concat(site.trunc(x, 8), site.trunc(x, 8)),
            site.select(site.cmp("eq", x, one), x, one),
        ]
        assert all(isinstance(h, int) for h in built)
        assert site.width(built[6]) == 16
        assert site.bin("add", x, site.trunc(x, 8)) is None  # a width mismatch
        assert site.zext(x, 8) is None
        with pytest.raises(ValueError):
            site.bin("frob", x, one)
        with pytest.raises(ValueError):
            site.un("add", x)
        with pytest.raises(ValueError):
            site.cmp("lt", x, one)
        return built[7]  # larger: not committed

    out, stats = bw.Engine("compile", trusted_rewrites=[bw.Rewrite("t.inspect", inspect)]).run(
        [e], stats=True
    )
    assert out[0].expr == e and seen and stats.host.rejected_cost > 0
    # A site is lent for the call only.
    with pytest.raises(RuntimeError):
        seen[0].width(e.handle)
    assert "expired" in repr(seen[0])

    # An exception leaves the node, reported as unraisable.
    reported = []
    monkeypatch.setattr("sys.unraisablehook", lambda u: reported.append(u.exc_value))

    def broken(site, n):
        raise KeyError("oops")

    out = bw.Engine("compile", trusted_rewrites=[bw.Rewrite("t.broken", broken)]).run([e])
    assert out[0].expr == e and reported and isinstance(reported[0], KeyError)
    reported.clear()
    # A result that is not a handle is reported too.
    not_a_handle = bw.Rewrite("t.text", lambda s, n: "x")  # type: ignore[arg-type,return-value]
    out = bw.Engine(trusted_rewrites=[not_a_handle]).run([e])
    assert out[0].expr == e and reported
    reported.clear()

    # Using the context being simplified from a rewrite is an error, not a deadlock.
    def uses_the_context(site, n):
        str(e)
        return None

    out = bw.Engine(trusted_rewrites=[bw.Rewrite("t.ctx", uses_the_context)]).run([e])
    assert out[0].expr == e and reported and "busy" in str(reported[0])
    with pytest.raises(TypeError):
        bw.Rewrite("t.none", None)  # type: ignore[arg-type]


def test_checking_host_rewrites():
    def xor_twice(site, n):
        if site.op(n) != "xor":
            return None
        a, y = site.children(n)
        if site.op(a) != "xor":
            return None
        x, z = site.children(a)
        return x if z == y else z if x == y else None

    def mul_pow2(site, n):
        if site.op(n) != "mul":
            return None
        x, c = site.children(n)
        v = site.value(c)
        if v is None or v & (v - 1):
            return None
        return site.bin("shl", x, site.constant(v.bit_length() - 1, site.width(n)))

    report = bw.check_rewrite(bw.Rewrite("t.xor", xor_twice), ["(x ^ y) ^ y", "((a + 1) ^ 7) ^ 7"])
    assert report and report.failure is None
    assert report.applications > 0 and report.exhaustive > 0 and report.points > 0
    assert "passed" in repr(report)
    assert bw.check_rewrite(bw.Rewrite("t.shl", mul_pow2), ["x * 8", "(a + b) * 2", "x * 6"])
    # Every assignment of two 4-bit symbols, at one width, without variations.
    small = bw.check_rewrite(bw.Rewrite("t.xor", xor_twice), ["(x ^ y) ^ y"], widths=[4], variants=0)
    assert (small.applications, small.points) == (1, 256)

    def wrong(site, n):
        return site.children(n)[0] if site.op(n) == "or" else None

    report = bw.check_rewrite(bw.Rewrite("t.wrong", wrong), ["x | y"], seed=7, samples=64)
    assert not report
    f = report.failure
    assert f is not None
    assert f.kind == "differs" and f.node == "x | y" and f.result == "x"
    assert set(f.assignment) == {"x", "y"}
    assert f.assignment["y"] & ~f.assignment["x"] != 0
    assert "differs at" in f.message and "differs" in repr(f)
    never = bw.check_rewrite(bw.Rewrite("t.xor", xor_twice), ["x + y"]).failure
    assert never is not None and never.kind == "never_applied" and never.node is None
    bad = bw.check_rewrite(bw.Rewrite("t.xor", xor_twice), ["x +"]).failure
    assert bad is not None and bad.kind == "unparsable" and bad.node == "x +"


def test_templates(cx):
    a, b = cx.symbols("a b", 32)
    c = cx.symbol("c", 1)
    pick = bw.Template("select(c, a + 1, b)", ["c", "a", "b"])
    assert pick.params == ["c", "a", "b"] and "c, a, b" in repr(pick)
    pick.check([1, 32, 32])
    with pytest.raises(bw.ParseError):
        pick.check([8, 8, 8])  # the condition must be 1 bit
    e = pick.instantiate([c, a, b])
    assert str(e) == "select(c, a + 1, b)" and pick.instantiate([c, a, b]) == e
    x = cx.symbol("x", 8)
    assert str(pick.instantiate([c, x, x])) == "select(c, x + 1, x)"
    with pytest.raises(bw.BitwrightError):
        pick.instantiate([a, b])
    with pytest.raises(bw.BitwrightError):
        bw.Template("a + a", ["a", "a"])
    with pytest.raises(bw.ParseError):
        bw.Template("a +", ["a"]).check([8])
    seven = bw.Template("7:16", [])
    assert str(seven.instantiate([], context=cx)) == "7:16"
    with pytest.raises(ValueError):
        seven.instantiate([])
    with pytest.raises(ValueError):
        pick.instantiate([c, a, bw.Context().symbol("b", 32)])


def test_lowering_and_raising(cx):
    lw = bw.Lowering(cx)
    assert lw.context is cx or lw.context.__class__ is bw.Context
    # %0 is a parameter known 16-byte aligned; %1 is read first when used.
    p = lw.input(0, 64, name="p", known=(15, 0))
    assert str(p) == "p" and cx.declared_known(p) == (15, 0)
    assert lw.input(0, 64) == p and lw.value(0, 64) == p
    v1 = lw.value(1, 64)
    assert str(v1) == "$0"
    with pytest.raises(bw.WidthError):
        lw.value(1, 32)
    v2 = p & v1
    lw.define(2, v2)
    v3 = v2 + p
    lw.define(3, v3)
    assert lw.get(3) == v3 and lw.get(9) is None
    assert lw.owner(v2) == 2 and lw.owner(p + 1) is None
    assert [(v, str(s)) for v, s in lw.inputs] == [(0, "p"), (1, "$0")]
    assert "2 inputs" in repr(lw)

    # (p & $0) + p ^ (p & 5): %3 is there; the mask and the xor are new.
    x = v3 ^ (p & 5)
    code = []

    def emit(node, operands):
        code.append((node.kind, node.op, operands))
        return 100 + len(code) - 1

    assert lw.raise_(x, emit) == 102
    assert code == [("const", None, []), ("binary", "and", [0, 100]), ("binary", "xor", [3, 101])]
    assert lw.raise_(x, emit) == 102 and lw.raise_(v3, emit) == 3 and len(code) == 3
    assert lw.owner(x) == 102
    # A symbol no host value stands for; an emit that fails leaves what it did.
    with pytest.raises(bw.BitwrightError):
        lw.raise_(x - cx.symbol("stray", 64), emit)

    def fails(node, operands):
        raise ValueError("no such instruction")

    with pytest.raises(ValueError):
        lw.raise_(p * v1, fails)
    with pytest.raises(TypeError):
        lw.raise_(p * v1, lambda node, operands: "r1")  # type: ignore[arg-type,return-value]
    # The emit callback may use the context.
    assert lw.raise_(p * v1, lambda node, operands: len(str(node))) == len("p * $0")
    # Known bits of the wrong width or in conflict; an expression of another context.
    with pytest.raises(ValueError):
        lw.input(7, 8, known=(0x100, 0))
    with pytest.raises(ValueError):
        lw.input(7, 8, known=(1, 1))
    with pytest.raises(ValueError):
        lw.define(8, bw.Context().symbol("f", 64))


def test_version():
    assert bw.__version__.count(".") == 2


def test_the_book_examples():
    """Every Python example of the book's chapters on the bindings and their examples runs (its
    checks are asserts)."""
    import pathlib

    book = pathlib.Path(__file__).parents[2] / "book" / "src"
    for chapter in (book / "bindings.md", book / "examples-bindings.md"):
        text = chapter.read_text()
        parts = text.split("```python\n")
        assert len(parts) > 1
        line = parts[0].count("\n") + 1
        for part in parts[1:]:
            code = part.split("```\n")[0]
            # Padded so that a failure reports the chapter's line numbers.
            exec(compile("\n" * line + code, str(chapter), "exec"), {})
            line += part.count("\n") + 1
