# Binary Ninja plugin: the low-level IL of the basic block at the cursor, deobfuscated by
# bitwright. Copy into the plugins folder; needs the `bitwright` Python package in Binary
# Ninja's interpreter.
#
# Written against Binary Ninja's documented Python API; not tested here (no Binary Ninja in the
# development environment). Unsupported IL operations are reported, not guessed.

import bitwright
from binaryninja import PluginCommand, log_error, log_info


class Lifter:
    """LLIL to bitwright expressions: registers by name, memory through a bitwright.Memory."""

    def __init__(self, cx, addr_bits):
        self.cx = cx
        self.regs = {}
        self.mem = bitwright.Memory(cx, "mem", addr_bits)
        self.stores = []

    def reg(self, name, size):
        if name not in self.regs:
            self.regs[name] = self.cx.symbol(name, 8 * size)
        v = self.regs[name]
        return v if v.width == 8 * size else v.trunc(8 * size)

    def expr(self, il):
        op = il.operation.name
        bits = 8 * il.size if il.size else None
        if op in ("LLIL_CONST", "LLIL_CONST_PTR"):
            return self.cx.const(il.constant & ((1 << bits) - 1), bits)
        if op == "LLIL_REG":
            return self.reg(str(il.src), il.size)
        if op == "LLIL_LOAD":
            return self.mem.load(self.expr(il.src), il.size)
        binary = {
            "LLIL_ADD": lambda a, b: a + b,
            "LLIL_SUB": lambda a, b: a - b,
            "LLIL_MUL": lambda a, b: a * b,
            "LLIL_AND": lambda a, b: a & b,
            "LLIL_OR": lambda a, b: a | b,
            "LLIL_XOR": lambda a, b: a ^ b,
            "LLIL_LSL": lambda a, b: a.shl(b),
            "LLIL_LSR": lambda a, b: a.lshr(b),
            "LLIL_ASR": lambda a, b: a.ashr(b),
            "LLIL_CMP_E": lambda a, b: a.eq(b),
            "LLIL_CMP_NE": lambda a, b: a.ne(b),
            "LLIL_CMP_ULT": lambda a, b: a.ult(b),
            "LLIL_CMP_ULE": lambda a, b: a.ule(b),
            "LLIL_CMP_UGT": lambda a, b: a.ugt(b),
            "LLIL_CMP_UGE": lambda a, b: a.uge(b),
            "LLIL_CMP_SLT": lambda a, b: a.slt(b),
            "LLIL_CMP_SLE": lambda a, b: a.sle(b),
            "LLIL_CMP_SGT": lambda a, b: a.sgt(b),
            "LLIL_CMP_SGE": lambda a, b: a.sge(b),
        }
        if op in binary:
            a, b = self.expr(il.left), self.expr(il.right)
            if op in ("LLIL_LSL", "LLIL_LSR", "LLIL_ASR") and b.width != a.width:
                b = b.zext(a.width) if b.width < a.width else b.trunc(a.width)
            return binary[op](a, b)
        if op == "LLIL_NEG":
            return -self.expr(il.src)
        if op == "LLIL_NOT":
            return ~self.expr(il.src)
        if op == "LLIL_ZX":
            return self.expr(il.src).zext(bits)
        if op == "LLIL_SX":
            return self.expr(il.src).sext(bits)
        if op == "LLIL_LOW_PART":
            return self.expr(il.src).trunc(bits)
        raise ValueError("bitwright does not read %s" % op)

    def statement(self, il):
        op = il.operation.name
        if op == "LLIL_SET_REG":
            self.regs[str(il.dest)] = self.expr(il.src)
        elif op == "LLIL_STORE":
            addr, value = self.expr(il.dest), self.expr(il.src)
            self.mem.store(addr, value)
            self.stores.append((addr, value))
        elif op in ("LLIL_NOP", "LLIL_GOTO", "LLIL_IF", "LLIL_JUMP", "LLIL_RET"):
            pass
        else:
            raise ValueError("bitwright does not read %s" % op)


def deobfuscate_block(bv, address):
    funcs = bv.get_functions_containing(address)
    if not funcs:
        log_error("no function at the cursor")
        return
    llil = funcs[0].llil
    block = next((b for b in llil if b.start <= llil.get_instruction_start(address) < b.end), None)
    if block is None:
        log_error("no IL block at the cursor")
        return
    cx = bitwright.Context()
    lifter = Lifter(cx, 8 * bv.address_size)
    try:
        for il in block:
            lifter.statement(il)
    except ValueError as e:
        log_error(str(e))
        return
    engine = bitwright.Engine.deobfuscate()
    for name, value in lifter.regs.items():
        if value.name != name:
            log_info("%s = %s" % (name, engine.simplify(value)))
    for addr, value in lifter.stores:
        log_info("store [%s] = %s" % (engine.simplify(addr), engine.simplify(value)))


PluginCommand.register_for_address(
    "bitwright\\Deobfuscate block",
    "The basic block's registers and stores, simplified by bitwright",
    deobfuscate_block,
)
