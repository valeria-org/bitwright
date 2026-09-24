"""Hash-consed fixed-width bit-vector expressions: exact evaluation, bit-level facts, and
verified simplification.

>>> import bitwright
>>> cx = bitwright.Context()
>>> x, y = cx.symbols("x y", 64)
>>> str(((x & y) + (x | y)).simplify())
'x + y'
>>> bitwright.simplify("(x ^ y) + 2 * (x & y)")
'x + y'

The guide is the bitwright book: https://valeria-org.github.io/bitwright/
"""

from ._bitwright import (
    BF16,
    F16,
    F32,
    F64,
    F128,
    F256,
    X87,
    Assumptions,
    BitwrightError,
    Budget,
    Context,
    Engine,
    Expr,
    Facts,
    FpFormat,
    Outcome,
    ParseError,
    RuleError,
    SmtScript,
    WidthError,
    __version__,
    check_rules,
    simplify,
)

__all__ = [
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
    "__version__",
    "check_rules",
    "simplify",
]
