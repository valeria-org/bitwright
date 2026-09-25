# IDA Pro with Hex-Rays: each arithmetic expression of the decompiled function at the cursor,
# simplified by bitwright, printed where it simplifies. Run as a script (File > Script file);
# needs the `bitwright` Python package in IDA's interpreter.
#
# Written against the Hex-Rays ctree API (ida_hexrays); not tested here (no IDA in the
# development environment).

import bitwright
import ida_hexrays
import ida_kernwin

BINARY = {
    ida_hexrays.cot_add: lambda a, b: a + b,
    ida_hexrays.cot_sub: lambda a, b: a - b,
    ida_hexrays.cot_mul: lambda a, b: a * b,
    ida_hexrays.cot_band: lambda a, b: a & b,
    ida_hexrays.cot_bor: lambda a, b: a | b,
    ida_hexrays.cot_xor: lambda a, b: a ^ b,
    ida_hexrays.cot_shl: lambda a, b: a.shl(b),
    ida_hexrays.cot_ushr: lambda a, b: a.lshr(b),
    ida_hexrays.cot_sshr: lambda a, b: a.ashr(b),
}


class Converter:
    def __init__(self, cx, cfunc):
        self.cx = cx
        self.cfunc = cfunc

    def expr(self, e):
        bits = 8 * e.type.get_size()
        if e.op == ida_hexrays.cot_num:
            return self.cx.const(e.numval() & ((1 << bits) - 1), bits)
        if e.op == ida_hexrays.cot_var:
            name = self.cfunc.get_lvars()[e.v.idx].name
            return self.cx.symbol(name, bits)
        if e.op in BINARY:
            a, b = self.expr(e.x), self.expr(e.y)
            if b.width != a.width:
                b = b.zext(a.width) if b.width < a.width else b.trunc(a.width)
            return BINARY[e.op](a, b)
        if e.op == ida_hexrays.cot_neg:
            return -self.expr(e.x)
        if e.op == ida_hexrays.cot_bnot:
            return ~self.expr(e.x)
        if e.op == ida_hexrays.cot_cast:
            inner = self.expr(e.x)
            if inner.width == bits:
                return inner
            return inner.trunc(bits) if inner.width > bits else inner.zext(bits)
        raise ValueError("not arithmetic")


class Visitor(ida_hexrays.ctree_visitor_t):
    def __init__(self, cfunc):
        super().__init__(ida_hexrays.CV_PARENTS)
        self.cfunc = cfunc
        self.engine = bitwright.Engine.deobfuscate()

    def visit_expr(self, e):
        # The largest arithmetic expressions only: skip operands of an arithmetic parent.
        parent = self.parent_expr()
        if e.op not in BINARY or (parent is not None and parent.op in BINARY):
            return 0
        cx = bitwright.Context()
        try:
            x = Converter(cx, self.cfunc).expr(e)
        except (ValueError, bitwright.BitwrightError):
            return 0
        s = self.engine.simplify(x)
        if s.dag_size() < x.dag_size():
            print("0x%x: %s\n    => %s" % (e.ea, x, s))
        return 0


def main():
    cfunc = ida_hexrays.decompile(ida_kernwin.get_screen_ea())
    if cfunc is None:
        print("no decompiled function at the cursor")
        return
    Visitor(cfunc).apply_to(cfunc.body, None)


main()
