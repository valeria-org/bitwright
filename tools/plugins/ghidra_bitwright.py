# Ghidra script (PyGhidra, Python 3): the basic block at the cursor, read from its raw p-code and
# deobfuscated by bitwright. Needs the `bitwright` Python package in PyGhidra's interpreter.
#
# Written against Ghidra's documented scripting API; not tested here (no Ghidra in the
# development environment). Report problems with the output of the p-code text it prints.
#
# @category Deobfuscation
# @menupath Tools.bitwright.Deobfuscate block

import bitwright
from ghidra.program.model.block import BasicBlockModel


def varnode(vn):
    """A varnode as bitwright's p-code front end reads it, registers by name."""
    size = vn.getSize()
    if vn.isRegister():
        reg = currentProgram.getRegister(vn.getAddress(), size)  # noqa: F821 (Ghidra global)
        if reg is not None:
            return "(register, %s, %d)" % (reg.getName(), size)
        return "(register, 0x%x, %d)" % (vn.getOffset(), size)
    if vn.isUnique():
        return "(unique, 0x%x, %d)" % (vn.getOffset(), size)
    if vn.isConstant():
        return "(const, 0x%x, %d)" % (vn.getOffset() & ((1 << 64) - 1), size)
    space = vn.getAddress().getAddressSpace().getName()
    return "(%s, 0x%x, %d)" % (space, vn.getOffset(), size)


def pcode_text(block):
    lines = []
    for instr in currentProgram.getListing().getInstructions(block, True):  # noqa: F821
        for op in instr.getPcode():
            out = op.getOutput()
            ins = ", ".join(varnode(v) for v in op.getInputs())
            head = (varnode(out) + " = ") if out is not None else ""
            lines.append("%s%s %s" % (head, op.getMnemonic(), ins))
    return "\n".join(lines)


def main():
    model = BasicBlockModel(currentProgram)  # noqa: F821
    blocks = model.getCodeBlocksContaining(currentAddress, monitor)  # noqa: F821
    if not blocks:
        print("no basic block at the cursor")
        return
    text = pcode_text(blocks[0])
    print("p-code:\n" + text)
    cx = bitwright.Context()
    try:
        block = bitwright.lift_pcode(cx, text)
    except bitwright.BitwrightError as e:
        print("bitwright could not read it: %s" % e)
        return
    engine = bitwright.Engine.deobfuscate()
    for name, e in block.outputs:
        print("%s = %s" % (name, engine.simplify(e)))
    for addr, value in block.stores:
        print("store [%s] = %s" % (engine.simplify(addr), engine.simplify(value)))
    for cond, target in block.exits:
        print("exit to %s if %s" % (engine.simplify(target), engine.simplify(cond)))


main()
