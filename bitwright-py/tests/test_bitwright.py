"""Tests of the Python bindings: `pip install ./bitwright-py pytest && pytest bitwright-py/tests`."""

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


def test_version():
    assert bw.__version__.count(".") == 2


def test_the_book_examples():
    """Every Python example of the book's chapter on the bindings runs (its checks are asserts)."""
    import pathlib

    chapter = pathlib.Path(__file__).parents[2] / "book" / "src" / "bindings.md"
    text = chapter.read_text()
    parts = text.split("```python\n")
    assert len(parts) > 1
    line = parts[0].count("\n") + 1
    for part in parts[1:]:
        code = part.split("```\n")[0]
        # Padded so that a failure reports the chapter's line numbers.
        exec(compile("\n" * line + code, str(chapter), "exec"), {})
        line += part.count("\n") + 1
