from collections.abc import Mapping, Sequence
from typing import Literal, TypeAlias, final

__version__: str
__all__ = [
    "__version__",
    "Assumptions",
    "BitwrightError",
    "Budget",
    "Context",
    "Engine",
    "Expr",
    "Facts",
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
    "select", "ext",
]

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
        """An SMT-LIB 2.6 QF_BV script defining the K-th expression as `rootK`."""
    def from_smtlib(self, script: str) -> SmtScript:
        """Reads an SMT-LIB QF_BV script into this context."""

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
        """The operator of a unary, binary or comparison node (`"add"`, `"ult"`, ...)."""
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
