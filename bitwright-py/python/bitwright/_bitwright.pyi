from collections.abc import Mapping, Sequence
from typing import Literal, TypeAlias, final

__version__: str
__all__ = [
    "__version__",
    "BF16",
    "F16",
    "F32",
    "F64",
    "F128",
    "F256",
    "X87",
    "Assumptions",
    "BitwrightError",
    "Budget",
    "Context",
    "Engine",
    "Expr",
    "Facts",
    "FpFormat",
    "Outcome",
    "ParseError",
    "RuleError",
    "SmtScript",
    "WidthError",
    "check_rules",
    "simplify",
]

class BitwrightError(Exception):
    """An error reported by bitwright."""

class WidthError(BitwrightError):
    """A width rule was violated: operands of different widths, a bad cast, a symbol used at two
    widths."""

class ParseError(BitwrightError):
    """A syntax or typing error in expression text or an SMT-LIB script."""

class RuleError(BitwrightError):
    """A rule file that does not compile or check, or an engine that does not link."""

_Kind: TypeAlias = Literal[
    "const", "symbol", "unary", "binary", "compare", "zext", "sext", "extract", "concat",
    "select", "ext", "fp",
]

_Rounding: TypeAlias = Literal["rne", "rna", "rtp", "rtn", "rtz"]

@final
class FpFormat:
    """A binary floating-point format: `eb` exponent bits and `sb` significand bits, the hidden
    bit included, so an encoding is `eb + sb` bits wide. Immutable and hashable."""

    def __new__(cls, eb: int, sb: int) -> FpFormat:
        """Raises `WidthError` unless `2 <= eb <= 31`, `sb >= 2` and `eb + sb <= 512`."""
    @property
    def eb(self) -> int:
        """Exponent bits."""
    @property
    def sb(self) -> int:
        """Significand bits, the hidden bit included (the precision)."""
    @property
    def width(self) -> int:
        """The width of an encoding: `eb + sb`."""
    @property
    def name(self) -> str | None:
        """The name of a standard format in the text syntax (`"f32"`, ...)."""
    def __eq__(self, other: object, /) -> bool: ...
    def __ne__(self, other: object, /) -> bool: ...
    def __hash__(self) -> int: ...

F16: FpFormat
"""IEEE binary16, `(5, 11)`."""
BF16: FpFormat
"""bfloat16, `(8, 8)`."""
F32: FpFormat
"""IEEE binary32, `(8, 24)`."""
F64: FpFormat
"""IEEE binary64, `(11, 53)`."""
F128: FpFormat
"""IEEE binary128, `(15, 113)`."""
F256: FpFormat
"""IEEE binary256, `(19, 237)`."""
X87: FpFormat
"""The values of x87 extended precision, `(15, 64)` (79 bits); see `Expr.x87_load`."""

@final
class Context:
    """A hash-consed expression arena. Every expression belongs to one context; structurally
    equal expressions of a context are one node (the same `Expr`). Safe to share between
    threads (operations on one context are serialized)."""

    def __new__(cls, *, max_nodes: int | None = None, fact_work: int | None = None) -> Context: ...
    def __len__(self) -> int: ...
    def clear(self) -> None:
        """Drops every node and symbol: every expression of the context becomes stale."""
    def symbol(self, name: str | int, width: int) -> Expr:
        """The symbol `name` of `width` bits (an int key prints as `#k`)."""
    def symbols(self, names: str, width: int) -> list[Expr]:
        """Symbols named by the words of `names` (e.g. `"x y z"`), all of `width` bits."""
    def fresh_symbol(self, width: int) -> Expr:
        """A symbol distinct from every other (printed `$k`)."""
    def const(self, value: int, width: int) -> Expr:
        """The constant `value` of `width` bits: `0 <= value < 2**width`, or a negative value
        in two's complement down to `-2**(width - 1)`."""
    def parse(self, text: str, width: int | None = None) -> Expr:
        """Parses expression text; `width` types what cannot be inferred."""
    def to_smtlib(self, *exprs: Expr) -> str:
        """An SMT-LIB 2.6 QF_BV script (QF_BVFP with floating point) defining the K-th
        expression as `rootK`."""
    def from_smtlib(self, script: str) -> SmtScript:
        """Reads an SMT-LIB QF_BV script, floating-point (QF_BVFP) terms included, into this
        context."""

@final
class SmtScript:
    symbols: dict[str, Expr]
    definitions: dict[str, Expr]
    assertions: list[Expr]

_Operand: TypeAlias = Expr | int

@final
class Expr:
    """An expression. Immutable and hashable; `==` is identity. Comparisons that build a 1-bit
    expression are methods (`eq`, `ult`, `slt`, ...). An int operand is a constant of the other
    operand's width."""

    @property
    def width(self) -> int: ...
    @property
    def context(self) -> Context: ...
    @property
    def handle(self) -> int: ...
    @property
    def kind(self) -> _Kind: ...
    @property
    def op(self) -> str | None:
        """The operator of a unary, binary, comparison or floating-point node (`"add"`, `"ult"`,
        `"sqrt"`, ...)."""
    @property
    def children(self) -> list[Expr]: ...
    @property
    def value(self) -> int | None:
        """The value of a constant, unsigned."""
    @property
    def signed_value(self) -> int | None:
        """The value of a constant, signed."""
    @property
    def name(self) -> str | None:
        """The name of a symbol."""
    @property
    def lo(self) -> int | None:
        """The first bit of an extract."""
    @property
    def format(self) -> FpFormat | None:
        """The format of a floating-point node's operands (of its result, from an integer)."""
    @property
    def to_format(self) -> FpFormat | None:
        """The result's format of a conversion between formats (`"convert"`)."""
    @property
    def rounding(self) -> _Rounding | None:
        """The rounding mode of a floating-point node that has one."""
    def dag_size(self) -> int: ...
    def to_string(self, *, lets: bool = True, symbol_widths: bool = False) -> str: ...
    def __hash__(self) -> int: ...
    def __eq__(self, other: object, /) -> bool: ...
    def __ne__(self, other: object, /) -> bool: ...
    def __bool__(self) -> bool:
        """Raises TypeError: use `prove()`."""
    def __add__(self, o: _Operand, /) -> Expr: ...
    def __radd__(self, o: _Operand, /) -> Expr: ...
    def __sub__(self, o: _Operand, /) -> Expr: ...
    def __rsub__(self, o: _Operand, /) -> Expr: ...
    def __mul__(self, o: _Operand, /) -> Expr: ...
    def __rmul__(self, o: _Operand, /) -> Expr: ...
    def __floordiv__(self, o: _Operand, /) -> Expr:
        """Unsigned division."""
    def __rfloordiv__(self, o: _Operand, /) -> Expr: ...
    def __mod__(self, o: _Operand, /) -> Expr:
        """Unsigned remainder."""
    def __rmod__(self, o: _Operand, /) -> Expr: ...
    def __and__(self, o: _Operand, /) -> Expr: ...
    def __rand__(self, o: _Operand, /) -> Expr: ...
    def __or__(self, o: _Operand, /) -> Expr: ...
    def __ror__(self, o: _Operand, /) -> Expr: ...
    def __xor__(self, o: _Operand, /) -> Expr: ...
    def __rxor__(self, o: _Operand, /) -> Expr: ...
    def __lshift__(self, o: _Operand, /) -> Expr: ...
    def __rlshift__(self, o: _Operand, /) -> Expr: ...
    def __rshift__(self, o: _Operand, /) -> Expr:
        """Logical right shift (`ashr` is the arithmetic one)."""
    def __rrshift__(self, o: _Operand, /) -> Expr: ...
    def __invert__(self) -> Expr: ...
    def __neg__(self) -> Expr: ...
    def udiv(self, o: _Operand) -> Expr: ...
    def urem(self, o: _Operand) -> Expr: ...
    def sdiv(self, o: _Operand) -> Expr: ...
    def srem(self, o: _Operand) -> Expr: ...
    def umulhi(self, o: _Operand) -> Expr: ...
    def smulhi(self, o: _Operand) -> Expr: ...
    def shl(self, o: _Operand) -> Expr: ...
    def lshr(self, o: _Operand) -> Expr: ...
    def ashr(self, o: _Operand) -> Expr: ...
    def rotl(self, o: _Operand) -> Expr: ...
    def rotr(self, o: _Operand) -> Expr: ...
    def pdep(self, o: _Operand) -> Expr: ...
    def pext(self, o: _Operand) -> Expr: ...
    def popcnt(self) -> Expr: ...
    def clz(self) -> Expr: ...
    def ctz(self) -> Expr: ...
    def bswap(self) -> Expr: ...
    def bitrev(self) -> Expr: ...
    def eq(self, o: _Operand) -> Expr: ...
    def ne(self, o: _Operand) -> Expr: ...
    def ult(self, o: _Operand) -> Expr: ...
    def ule(self, o: _Operand) -> Expr: ...
    def ugt(self, o: _Operand) -> Expr: ...
    def uge(self, o: _Operand) -> Expr: ...
    def slt(self, o: _Operand) -> Expr: ...
    def sle(self, o: _Operand) -> Expr: ...
    def sgt(self, o: _Operand) -> Expr: ...
    def sge(self, o: _Operand) -> Expr: ...
    def zext(self, width: int) -> Expr: ...
    def sext(self, width: int) -> Expr: ...
    def trunc(self, width: int) -> Expr: ...
    def extract(self, lo: int, length: int) -> Expr:
        """Bits `[lo, lo + length)`."""
    def bit(self, i: int) -> Expr:
        """Bit `i`, as a 1-bit expression."""
    def concat(self, *lows: Expr) -> Expr:
        """This expression in the high bits, then each of `lows`."""
    def select(self, then: _Operand, els: _Operand) -> Expr:
        """`then` where this 1-bit condition holds, else `els`."""
    # Floating point: this expression and the operands hold encodings of `fmt` (an int operand
    # is one), and a result is rounded by `rm`.
    def fadd(self, o: _Operand, fmt: FpFormat, rm: _Rounding = "rne") -> Expr: ...
    def fsub(self, o: _Operand, fmt: FpFormat, rm: _Rounding = "rne") -> Expr: ...
    def fmul(self, o: _Operand, fmt: FpFormat, rm: _Rounding = "rne") -> Expr: ...
    def fdiv(self, o: _Operand, fmt: FpFormat, rm: _Rounding = "rne") -> Expr: ...
    def ffma(self, b: _Operand, c: _Operand, fmt: FpFormat, rm: _Rounding = "rne") -> Expr:
        """`self * b + c`, rounded once."""
    def fsqrt(self, fmt: FpFormat, rm: _Rounding = "rne") -> Expr: ...
    def frem(self, o: _Operand, fmt: FpFormat) -> Expr:
        """The IEEE remainder (exact)."""
    def fround(self, fmt: FpFormat, rm: _Rounding = "rne") -> Expr:
        """Rounded to an integral value."""
    def fmin(self, o: _Operand, fmt: FpFormat) -> Expr:
        """minimumNumber: a NaN operand ignored, `-0 < +0`."""
    def fmax(self, o: _Operand, fmt: FpFormat) -> Expr:
        """maximumNumber: a NaN operand ignored, `-0 < +0`."""
    def feq(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def flt(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def fle(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def fgt(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def fge(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def fneg(self, fmt: FpFormat) -> Expr: ...
    def fabs(self, fmt: FpFormat) -> Expr: ...
    def fcopysign(self, o: _Operand, fmt: FpFormat) -> Expr: ...
    def fisnan(self, fmt: FpFormat) -> Expr: ...
    def fisinf(self, fmt: FpFormat) -> Expr: ...
    def fiszero(self, fmt: FpFormat) -> Expr: ...
    def fissubnormal(self, fmt: FpFormat) -> Expr: ...
    def fisnormal(self, fmt: FpFormat) -> Expr: ...
    def fisneg(self, fmt: FpFormat) -> Expr: ...
    def fispos(self, fmt: FpFormat) -> Expr: ...
    def fconvert(self, to: FpFormat, fmt: FpFormat, rm: _Rounding = "rne") -> Expr:
        """This value of format `fmt` converted to the format `to`."""
    def to_float(self, fmt: FpFormat, rm: _Rounding = "rne", *, signed: bool = True) -> Expr:
        """This integer rounded to the format `fmt`."""
    def to_int(
        self, width: int, fmt: FpFormat, rm: _Rounding = "rne", *, signed: bool = True
    ) -> Expr:
        """This value of format `fmt` rounded to a `width`-bit integer, saturating (a NaN gives
        0)."""
    def x87_load(self) -> Expr:
        """x87's 80-bit encoding as a value of `X87`."""
    def x87_store(self) -> Expr:
        """A value of `X87` as x87's 80-bit encoding."""
    def eval(self, env: Mapping[str | int | Expr, int] | None = None, /, **kwargs: int) -> int:
        """The value (unsigned) with symbols bound by name or by symbol expression."""
    def substitute(self, mapping: Mapping[Expr, _Operand]) -> Expr:
        """Every key replaced by its value, all at once."""
    def facts(self, assumptions: Assumptions | None = None) -> Facts: ...
    def prove(self, assumptions: Assumptions | None = None) -> bool | None:
        """Whether the expression is nonzero (a predicate: whether it holds); None when not
        decided."""
    def prove_injective(
        self, of: Expr, *, bijective: bool = False, assumptions: Assumptions | None = None
    ) -> bool | None: ...
    def simplify(self, engine: Engine | None = None) -> Expr: ...

@final
class Facts:
    """What is known about every value of an expression."""

    width: int
    known_zero: int
    known_one: int
    umin: int
    umax: int
    ustride: int
    smin: int
    smax: int
    constant: int | None
    relies_on: tuple[int, ...]

@final
class Assumptions:
    """Constraints known to hold, numbered from 0 in the order they are added."""

    def __new__(cls, *predicates: Expr) -> Assumptions: ...
    def assume(self, predicate: Expr, holds: bool = True) -> int: ...
    @property
    def infeasible(self) -> bool: ...
    def __len__(self) -> int: ...

@final
class Budget:
    """Caps on the work of one call; each an int, or None for unlimited."""

    def __new__(
        cls,
        *,
        node_visits: int | None = ...,
        candidates: int | None = ...,
        match_steps: int | None = ...,
        rewrites: int | None = ...,
        new_nodes: int | None = ...,
        fact_work: int | None = ...,
        pass_work: int | None = ...,
        mba_calls: int | None = ...,
        eqsat_nodes: int | None = ...,
        eqsat_work: int | None = ...,
    ) -> Budget: ...
    @staticmethod
    def unlimited() -> Budget: ...
    @property
    def node_visits(self) -> int | None: ...
    @property
    def candidates(self) -> int | None: ...
    @property
    def match_steps(self) -> int | None: ...
    @property
    def rewrites(self) -> int | None: ...
    @property
    def new_nodes(self) -> int | None: ...
    @property
    def fact_work(self) -> int | None: ...
    @property
    def pass_work(self) -> int | None: ...
    @property
    def mba_calls(self) -> int | None: ...
    @property
    def eqsat_nodes(self) -> int | None: ...
    @property
    def eqsat_work(self) -> int | None: ...

@final
class Outcome:
    expr: Expr
    changed: bool
    end: Literal["completed", "budget", "declined"]
    limit: str | None
    relies_on: tuple[int, ...]

@final
class Engine:
    """A simplifier: `"standard"` or `"deobfuscate"`, with rule files of your own."""

    def __new__(
        cls,
        preset: Literal["standard", "deobfuscate"] = "standard",
        *,
        rules: Sequence[str | tuple[str, str | None]] = ...,
        max_rounds: int | None = None,
    ) -> Engine: ...
    @staticmethod
    def standard() -> Engine: ...
    @staticmethod
    def deobfuscate() -> Engine: ...
    def simplify(
        self, expr: Expr, *, budget: Budget | None = None, assumptions: Assumptions | None = None
    ) -> Expr: ...
    def run(
        self,
        exprs: Sequence[Expr],
        *,
        budget: Budget | None = None,
        assumptions: Assumptions | None = None,
    ) -> list[Outcome]: ...

def check_rules(source: str) -> str:
    """Checks every rule of a `.bwr` source; the proof ledger vouching for them."""

def simplify(
    text: str, width: int = 64, *, deobfuscate: bool = True, assume: Sequence[str] = ...
) -> str:
    """Simplifies expression text, like the command line's `simplify`."""
