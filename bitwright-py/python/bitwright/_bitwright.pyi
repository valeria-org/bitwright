from collections.abc import Callable, Mapping, Sequence
from typing import Literal, TypeAlias, final, overload

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
    "Memory",
    "LiftedBlock",
    "TransformReport",
    "InferredPrecondition",
    "equivalent",
    "synthesize",
    "saturate",
    "lift_pcode",
    "lift_vex",
    "lift_llvm",
    "verify_transforms",
    "validate_functions",
    "infer_preconditions",
    "Rewrite",
    "Site",
    "RewriteReport",
    "RewriteFailure",
    "Stats",
    "PassStats",
    "Template",
    "Lowering",
    "check_rewrite",
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
    def reserve(self, additional: int) -> None:
        """Makes room for `additional` more nodes (a host about to build a function)."""
    def declare_known(self, sym: Expr, known: tuple[int, int]) -> None:
        """Declares the `(zero, one)` masks of the bits the host knows are 0 and 1 in symbol
        `sym`'s value; part of the symbol's meaning from then on. `(0, 0)` removes it."""
    def declared_known(self, sym: Expr) -> tuple[int, int] | None:
        """The `(zero, one)` masks declared for symbol `sym`, or None."""
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
    def equivalent(self, other: Expr, *, conflicts: int = 1000000) -> bool | dict[str, int] | None:
        """True (proved equal), a dict of symbol values where they differ, or None."""
    def synthesize(self, *, max_size: int = 7) -> Expr | None:
        """The smallest equal expression synthesis finds (proved), or None."""
    def saturate(self, *, groups: Sequence[str] | None = None) -> Expr | None:
        """The equality-saturation search's smaller candidate, or None."""

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
    """A simplifier: `"standard"`, `"deobfuscate"` or `"compile"`, with rule files and host
    rewrites of your own."""

    def __new__(
        cls,
        preset: Literal["standard", "deobfuscate", "compile"] = "standard",
        *,
        rules: Sequence[str | tuple[str, str | None]] = ...,
        max_rounds: int | None = None,
        float_values: bool = False,
        refuse: Sequence[str] = ...,
        sharing: Literal["roots", "ignored"] | None = None,
        max_region: int | None = None,
        rewrites: Sequence[Rewrite] = ...,
        trusted_rewrites: Sequence[Rewrite] = ...,
    ) -> Engine: ...
    @staticmethod
    def standard() -> Engine: ...
    @staticmethod
    def deobfuscate() -> Engine: ...
    @staticmethod
    def compile() -> Engine:
        """For a compiler, which simplifies every value of every function."""
    def simplify(
        self, expr: Expr, *, budget: Budget | None = None, assumptions: Assumptions | None = None
    ) -> Expr: ...
    def trace(
        self, expr: Expr, *, budget: Budget | None = None, assumptions: Assumptions | None = None
    ) -> tuple[Expr, list[tuple[str, Expr, Expr]]]:
        """The expression simplified, and each rewrite: (rule or pass, before, after)."""
    @overload
    def run(
        self,
        exprs: Sequence[Expr],
        *,
        budget: Budget | None = None,
        assumptions: Assumptions | None = None,
        stats: Literal[False] = False,
    ) -> list[Outcome]: ...
    @overload
    def run(
        self,
        exprs: Sequence[Expr],
        *,
        budget: Budget | None = None,
        assumptions: Assumptions | None = None,
        stats: Literal[True],
    ) -> tuple[list[Outcome], Stats]: ...
    @overload
    def run_each(
        self,
        exprs: Sequence[Expr],
        *,
        threads: int = 0,
        budget: Budget | None = None,
        assumptions: Assumptions | None = None,
        stats: Literal[False] = False,
    ) -> list[Outcome]:
        """Each expression simplified on its own, on up to `threads` threads (0: all)."""
    @overload
    def run_each(
        self,
        exprs: Sequence[Expr],
        *,
        threads: int = 0,
        budget: Budget | None = None,
        assumptions: Assumptions | None = None,
        stats: Literal[True],
    ) -> tuple[list[Outcome], Stats]: ...

@final
class PassStats:
    """Counters of one pass, or of the host rewrites together."""

    calls: int
    noop: int
    changed: int
    rejected_cost: int
    rejected: int
    atomized: int

@final
class Stats:
    """Counters of one simplification call (`Engine.run(..., stats=True)`)."""

    node_visits: int
    memo_hits: int
    candidates: int
    match_steps: int
    no_match: int
    guard_false: int
    degraded: int
    no_change: int
    rewrites: int
    hook_vetoes: int
    rejected: int
    cycles_cut: int
    quarantined: int
    new_nodes: int
    fact_work: int
    pass_work: int
    rounds: int
    passes: dict[str, PassStats]
    host: PassStats

def check_rules(source: str) -> str:
    """Checks every rule of a `.bwr` source; the proof ledger vouching for them."""

def simplify(
    text: str, width: int = 64, *, deobfuscate: bool = True, assume: Sequence[str] = ...
) -> str:
    """Simplifies expression text, like the command line's `simplify`."""

def equivalent(a: Expr, b: Expr, *, conflicts: int = 1000000) -> bool | dict[str, int] | None:
    """Whether `a` equals `b` for every value of the symbols: True, a counterexample, or None."""

def synthesize(e: Expr, *, max_size: int = 7) -> Expr | None:
    """The smallest expression equal to `e` that synthesis finds (proved), or None."""

def saturate(e: Expr, *, groups: Sequence[str] | None = None) -> Expr | None:
    """The equality-saturation search's candidate for `e`, or None."""

@final
class Memory:
    """A memory of a context: loads and stores as expressions."""

    def __new__(
        cls,
        ctx: Context,
        name: str = "mem",
        addr_width: int = 64,
        cell_width: int = 8,
        *,
        big_endian: bool = False,
        zeroed: bool = False,
    ) -> Memory: ...
    def set_bytes(self, start: int, data: Sequence[int] | bytes) -> None:
        """Known contents from address `start` on (8-bit cells), before any load or store."""
    def store(self, addr: Expr, value: Expr) -> None: ...
    def load(self, addr: Expr, cells: int = 1) -> Expr: ...
    def reads(self) -> list[tuple[Expr, Expr]]:
        """The reads of unknown cells so far: (address, symbol)."""

@final
class LiftedBlock:
    """A block of lifted code, read into expressions."""

    inputs: list[tuple[str, Expr]]
    outputs: list[tuple[str, Expr]]
    stores: list[tuple[Expr, Expr]]
    exits: list[tuple[Expr, Expr]]
    next: Expr | None
    def register(self, name: str) -> Expr | None: ...

def lift_pcode(ctx: Context, text: str) -> LiftedBlock:
    """Ghidra p-code, one operation per line."""

def lift_vex(ctx: Context, text: str) -> LiftedBlock:
    """VEX IR as pyvex prints an IRSB."""

def lift_llvm(ctx: Context, text: str, function: str | None = None) -> LiftedBlock:
    """A function of an LLVM IR module: its return value is the output `ret`."""

@final
class TransformReport:
    name: str
    verdict: Literal["valid", "invalid", "unknown", "unsupported"]
    text: str

@final
class InferredPrecondition:
    name: str
    pre: str | None
    weakest: bool
    verdict: Literal["valid", "invalid", "unknown", "unsupported"] | None

def verify_transforms(
    text: str, *, widths: Sequence[int] | None = None, conflicts: int | None = None
) -> list[TransformReport]:
    """Verifies transformations in the syntax of the Alive paper."""

def validate_functions(
    src: str, tgt: str | None = None, *, conflicts: int | None = None
) -> list[TransformReport]:
    """Translation validation of LLVM IR functions."""

def infer_preconditions(text: str) -> list[InferredPrecondition]:
    """Infers each transformation's precondition over its symbolic constants."""

# ----- in a compiler ----------------------------------------------------------------------

_UnOp: TypeAlias = Literal["not", "neg", "popcnt", "clz", "ctz", "bswap", "bitrev"]
_BinOp: TypeAlias = Literal[
    "add", "sub", "mul", "umulhi", "smulhi", "udiv", "urem", "sdiv", "srem", "and", "or", "xor",
    "shl", "lshr", "ashr", "rotl", "rotr", "pdep", "pext",
]
_CmpOp: TypeAlias = Literal["eq", "ne", "ult", "ule", "ugt", "uge", "slt", "sle", "sgt", "sge"]

@final
class Site:
    """What a host rewrite may do at a node, on integer handles of the context being
    simplified. Valid during the rewrite call only; a request the budget declines is None."""

    def kind(self, e: int) -> _Kind | Literal["other"] | None: ...
    def op(self, e: int) -> str | None: ...
    def children(self, e: int) -> list[int]: ...
    def lo(self, e: int) -> int | None: ...
    def width(self, e: int) -> int | None: ...
    def value(self, e: int) -> int | None: ...
    def facts(self, e: int) -> Facts | None: ...
    def to_string(self, e: int, *, lets: bool = True) -> str | None: ...
    def constant(self, value: int, width: int) -> int | None: ...
    def un(self, op: _UnOp, a: int) -> int | None: ...
    def bin(self, op: _BinOp, a: int, b: int) -> int | None: ...
    def cmp(self, op: _CmpOp, a: int, b: int) -> int | None: ...
    def zext(self, a: int, width: int) -> int | None: ...
    def sext(self, a: int, width: int) -> int | None: ...
    def trunc(self, a: int, width: int) -> int | None: ...
    def extract(self, a: int, lo: int, length: int) -> int | None: ...
    def concat(self, hi: int, lo: int) -> int | None: ...
    def select(self, cond: int, then: int, els: int) -> int | None: ...

@final
class Rewrite:
    """A host rewrite: `function(site, node)` returns the node's replacement (a handle built
    through the site) or None to leave it."""

    def __new__(
        cls,
        name: str,
        function: Callable[[Site, int], int | None],
        *,
        group: str = ...,
        revision: int = 1,
    ) -> Rewrite: ...
    @property
    def name(self) -> str: ...
    @property
    def group(self) -> str: ...
    @property
    def revision(self) -> int: ...

@final
class RewriteFailure:
    kind: Literal[
        "unparsable", "never_applied", "differs", "width", "not_smaller", "nondeterministic",
        "foreign_expr", "other",
    ]
    message: str
    node: str | None
    result: str | None
    second: str | None
    assignment: dict[str, int]

@final
class RewriteReport:
    """What `check_rewrite` covered, or why it failed: true when it passed."""

    applications: int
    points: int
    exhaustive: int
    failure: RewriteFailure | None
    def __bool__(self) -> bool: ...

def check_rewrite(
    rewrite: Rewrite,
    inputs: Sequence[str],
    *,
    widths: Sequence[int] | None = None,
    variants: int | None = None,
    max_exhaustive_bits: int | None = None,
    samples: int | None = None,
    seed: int | None = None,
) -> RewriteReport:
    """Tests a host rewrite offline on expression text: testing, not proof."""

@final
class Template:
    """An instruction's semantics as an expression over named parameters, read at run time."""

    def __new__(cls, text: str, params: Sequence[str]) -> Template: ...
    @property
    def params(self) -> list[str]: ...
    def check(self, widths: Sequence[int]) -> None: ...
    def instantiate(self, args: Sequence[Expr], context: Context | None = None) -> Expr: ...

@final
class Lowering:
    """One function of the host's IR translated into expressions of a context; host values are
    non-negative ints of the host's choosing."""

    def __new__(cls, context: Context) -> Lowering: ...
    @property
    def context(self) -> Context: ...
    def value(self, v: int, width: int) -> Expr: ...
    def input(
        self, v: int, width: int, *, name: str | None = None, known: tuple[int, int] | None = None
    ) -> Expr: ...
    def define(self, v: int, e: Expr) -> None: ...
    def get(self, v: int) -> Expr | None: ...
    def owner(self, e: Expr) -> int | None: ...
    @property
    def inputs(self) -> list[tuple[int, Expr]]: ...
    def raise_(self, e: Expr, emit: Callable[[Expr, list[int]], int]) -> int:
        """Turns `e` into host instructions: the value computing it; `emit(node, operands)`
        emits each node no host value computes, operands first."""
