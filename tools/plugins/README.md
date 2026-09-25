# Disassembler plugins

Scripts that hand the code at the cursor to bitwright's Python package (`pip install
./bitwright-py`, into the tool's interpreter) and print what it simplifies to:

- `ghidra_bitwright.py` (PyGhidra): the basic block's raw p-code, through
  `bitwright.lift_pcode`, registers by name.
- `binja_bitwright.py` (Binary Ninja plugin): the basic block's low-level IL, converted to
  bitwright expressions (memory through `bitwright.Memory`).
- `ida_bitwright.py` (IDA Pro with Hex-Rays): each arithmetic expression of the decompiled
  function, converted from the ctree.

They are written against each tool's documented Python API and have **not been tested**: none
of the tools is available where bitwright is developed. The front ends they rely on are tested
(`bitwright lift` reads p-code, VEX and LLVM IR text; see the book's chapter on lifted code),
so a problem is most likely in the conversion code of a script. Reports with the text a script
printed are welcome.
