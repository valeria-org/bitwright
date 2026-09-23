#!/usr/bin/env python3
"""Simplifies dataset expressions with other symbolic engines, for bitwright-compare.

    solvers.py ENGINE REQUEST RESPONSE
    solvers.py ENGINE --check

ENGINE is z3, bitwuzla, cvc5, claripy, miasm, triton-llvm or triton-synth. REQUEST holds one
expression per line in the datasets' syntax (C-like infix, 64-bit unsigned values), which is
also valid Python: it is parsed with Python's `ast` and built straight into the engine's terms,
so every engine starts from the same text. RESPONSE gets one line per expression: the
microseconds the simplification call took (building the terms is not timed), a tab, and an
SMT-LIB script declaring the variables and defining `answer__`, or `!` and an error. `--check`
exits 0 if the engine's Python package imports.

Each expression runs in a worker process that is killed, and the case answered `!timeout`, if it
takes longer than SOLVERS_TIMEOUT seconds (default 5, egg's default time limit): the engines are
native code that no Python-level alarm can interrupt.

Packages: z3-solver, bitwuzla, cvc5, claripy, triton-library, and Miasm (a source checkout on
PYTHONPATH, with the `future` package).
"""

import ast
import multiprocessing as mp
import os
import sys
import time

W = 64
MASK = (1 << W) - 1


def build(text, a):
    """Builds `text` with adapter `a` (var, const, bin(op, x, y), neg, not_)."""

    def go(n):
        if isinstance(n, ast.Expression):
            return go(n.body)
        if isinstance(n, ast.BinOp):
            op = {
                ast.Add: "+", ast.Sub: "-", ast.Mult: "*", ast.BitAnd: "&", ast.BitOr: "|",
                ast.BitXor: "^", ast.LShift: "<<", ast.RShift: ">>",
            }[type(n.op)]
            return a.bin(op, go(n.left), go(n.right))
        if isinstance(n, ast.UnaryOp):
            x = go(n.operand)
            if isinstance(n.op, ast.USub):
                return a.neg(x)
            if isinstance(n.op, ast.Invert):
                return a.not_(x)
            if isinstance(n.op, ast.UAdd):
                return x
        if isinstance(n, ast.Constant) and isinstance(n.value, int):
            return a.const(n.value & MASK)
        if isinstance(n, ast.Name):
            return a.var(n.id)
        raise ValueError(f"unsupported syntax: {ast.dump(n)[:60]}")

    return go(ast.parse(text.strip(), mode="eval"))


def names(text):
    return sorted({n.id for n in ast.walk(ast.parse(text.strip(), mode="eval")) if isinstance(n, ast.Name)})


def script(text, term):
    """A one-line SMT-LIB script: the variables' declarations and `answer__`."""
    decls = "".join(f"(declare-const {v} (_ BitVec {W})) " for v in names(text))
    return decls + f"(define-fun answer__ () (_ BitVec {W}) {term})"


class Z3:
    def __init__(self):
        import z3
        self.z3 = z3

    def var(self, n):
        return self.z3.BitVec(n, W)

    def const(self, v):
        return self.z3.BitVecVal(v, W)

    def bin(self, op, x, y):
        z = self.z3
        return {"+": lambda: x + y, "-": lambda: x - y, "*": lambda: x * y, "&": lambda: x & y,
                "|": lambda: x | y, "^": lambda: x ^ y, "<<": lambda: x << y,
                ">>": lambda: z.LShR(x, y)}[op]()

    def neg(self, x):
        return -x

    def not_(self, x):
        return ~x

    def simplify(self, t):
        return self.z3.simplify(t)

    def smt(self, t):
        return t.sexpr()


class Bitwuzla:
    def __init__(self):
        import bitwuzla as bw
        self.bw = bw
        self.tm = bw.TermManager()
        self.solver = bw.Bitwuzla(self.tm, bw.Options())
        self.sort = self.tm.mk_bv_sort(W)
        self.vars = {}

    def var(self, n):
        if n not in self.vars:
            self.vars[n] = self.tm.mk_const(self.sort, n)
        return self.vars[n]

    def const(self, v):
        return self.tm.mk_bv_value(self.sort, v)

    def bin(self, op, x, y):
        k = self.bw.Kind
        kind = {"+": k.BV_ADD, "-": k.BV_SUB, "*": k.BV_MUL, "&": k.BV_AND, "|": k.BV_OR,
                "^": k.BV_XOR, "<<": k.BV_SHL, ">>": k.BV_SHR}[op]
        return self.tm.mk_term(kind, [x, y])

    def neg(self, x):
        return self.tm.mk_term(self.bw.Kind.BV_NEG, [x])

    def not_(self, x):
        return self.tm.mk_term(self.bw.Kind.BV_NOT, [x])

    def simplify(self, t):
        return self.solver.simplify_term(t)

    def smt(self, t):
        return str(t)


class Cvc5:
    def __init__(self):
        import cvc5
        self.cvc5 = cvc5
        self.tm = cvc5.TermManager()
        self.solver = cvc5.Solver(self.tm)
        self.sort = self.tm.mkBitVectorSort(W)
        self.vars = {}

    def var(self, n):
        if n not in self.vars:
            self.vars[n] = self.tm.mkConst(self.sort, n)
        return self.vars[n]

    def const(self, v):
        return self.tm.mkBitVector(W, v)

    def bin(self, op, x, y):
        k = self.cvc5.Kind
        kind = {"+": k.BITVECTOR_ADD, "-": k.BITVECTOR_SUB, "*": k.BITVECTOR_MULT,
                "&": k.BITVECTOR_AND, "|": k.BITVECTOR_OR, "^": k.BITVECTOR_XOR,
                "<<": k.BITVECTOR_SHL, ">>": k.BITVECTOR_LSHR}[op]
        return self.tm.mkTerm(kind, x, y)

    def neg(self, x):
        return self.tm.mkTerm(self.cvc5.Kind.BITVECTOR_NEG, x)

    def not_(self, x):
        return self.tm.mkTerm(self.cvc5.Kind.BITVECTOR_NOT, x)

    def simplify(self, t):
        return self.solver.simplify(t)

    def smt(self, t):
        return str(t)


class Claripy:
    def __init__(self):
        import claripy
        self.c = claripy

    def var(self, n):
        return self.c.BVS(n, W, explicit_name=True)

    def const(self, v):
        return self.c.BVV(v, W)

    def bin(self, op, x, y):
        return {"+": lambda: x + y, "-": lambda: x - y, "*": lambda: x * y, "&": lambda: x & y,
                "|": lambda: x | y, "^": lambda: x ^ y, "<<": lambda: x << y,
                ">>": lambda: self.c.LShR(x, y)}[op]()

    def neg(self, x):
        return -x

    def not_(self, x):
        return ~x

    def simplify(self, t):
        return self.c.simplify(t)

    def smt(self, t):
        return self.c.backends.z3.convert(t).sexpr()


class Miasm:
    def __init__(self):
        from miasm.expression.expression import ExprId, ExprInt, ExprOp
        from miasm.expression.simplifications import expr_simp
        self.Id, self.Int, self.Op, self.simp = ExprId, ExprInt, ExprOp, expr_simp

    def var(self, n):
        return self.Id(n, W)

    def const(self, v):
        return self.Int(v, W)

    def bin(self, op, x, y):
        return self.Op(op, x, y)

    def neg(self, x):
        return self.Op("-", x)

    def not_(self, x):
        return self.Op("^", x, self.Int(MASK, W))

    def simplify(self, t):
        return self.simp(t)

    def smt(self, t):
        from miasm.expression.expression import ExprId, ExprInt, ExprOp
        if isinstance(t, ExprInt):
            return f"(_ bv{int(t)} {W})"
        if isinstance(t, ExprId):
            return str(t.name)
        if isinstance(t, ExprOp):
            args = [self.smt(a) for a in t.args]
            if t.op == "-" and len(args) == 1:
                return f"(bvneg {args[0]})"
            fn = {"+": "bvadd", "-": "bvsub", "*": "bvmul", "&": "bvand", "|": "bvor",
                  "^": "bvxor", "<<": "bvshl", ">>": "bvlshr", "a>>": "bvashr"}.get(t.op)
            if fn is None:
                raise ValueError(f"miasm operator {t.op}")
            out = args[0]
            for a in args[1:]:
                out = f"({fn} {out} {a})"
            return out
        raise ValueError(f"miasm expression {type(t).__name__}")


class Triton:
    def __init__(self, mode):
        from triton import TritonContext, ARCH, AST_REPRESENTATION
        self.ctx = TritonContext(ARCH.X86_64)
        self.ctx.setAstRepresentationMode(AST_REPRESENTATION.SMT)
        self.ast = self.ctx.getAstContext()
        self.mode = mode
        self.vars = {}

    def var(self, n):
        if n not in self.vars:
            self.vars[n] = self.ast.variable(self.ctx.newSymbolicVariable(W, n))
        return self.vars[n]

    def const(self, v):
        return self.ast.bv(v, W)

    def bin(self, op, x, y):
        a = self.ast
        return {"+": a.bvadd, "-": a.bvsub, "*": a.bvmul, "&": a.bvand, "|": a.bvor,
                "^": a.bvxor, "<<": a.bvshl, ">>": a.bvlshr}[op](x, y)

    def neg(self, x):
        return self.ast.bvneg(x)

    def not_(self, x):
        return self.ast.bvnot(x)

    def simplify(self, t):
        if self.mode == "llvm":
            return self.ctx.simplify(t, llvm=True)
        out = self.ctx.synthesize(t, constant=True, subexpr=True, opaque=False)
        return t if out is None else out

    def smt(self, t):
        return str(t)


ENGINES = {
    "z3": (Z3, "z3"),
    "bitwuzla": (Bitwuzla, "bitwuzla"),
    "cvc5": (Cvc5, "cvc5"),
    "claripy": (Claripy, "claripy"),
    "miasm": (Miasm, "miasm.expression.simplifications"),
    "triton-llvm": (lambda: Triton("llvm"), "triton"),
    "triton-synth": (lambda: Triton("synth"), "triton"),
}


def worker(name, conn):
    """Answers expressions from `conn` with engine `name`: (microseconds, term or `!error`)."""
    engine = ENGINES[name][0]()
    while True:
        text = conn.recv()
        if text is None:
            return
        try:
            term = build(text, engine)
            t = time.perf_counter()
            simplified = engine.simplify(term)
            us = (time.perf_counter() - t) * 1e6
            conn.send((us, " ".join(engine.smt(simplified).split())))
        except Exception as e:  # noqa: BLE001 - any failure is that case's answer
            conn.send((0.0, "!" + " ".join(str(e).split())))


def main():
    if len(sys.argv) == 3 and sys.argv[2] == "--check" and sys.argv[1] in ENGINES:
        __import__(ENGINES[sys.argv[1]][1])
        return 0
    if len(sys.argv) != 4 or sys.argv[1] not in ENGINES:
        print(__doc__, file=sys.stderr)
        return 2
    name = sys.argv[1]
    timeout = float(os.environ.get("SOLVERS_TIMEOUT", "5"))
    mpc = mp.get_context("fork")

    def start():
        parent, child = mpc.Pipe()
        p = mpc.Process(target=worker, args=(name, child), daemon=True)
        p.start()
        return p, parent

    proc, conn = start()
    with open(sys.argv[2]) as f:
        lines = [l.rstrip("\n") for l in f]
    with open(sys.argv[3], "w") as out:
        for text in lines:
            conn.send(text)
            if conn.poll(timeout):
                us, answer = conn.recv()
                if answer.startswith("!"):
                    out.write(f"{us:.1f}\t{answer}\n")
                else:
                    out.write(f"{us:.1f}\t{script(text, answer)}\n")
            else:
                proc.kill()
                proc.join()
                out.write(f"{timeout * 1e6:.1f}\t!timeout after {timeout:g} s\n")
                proc, conn = start()
            out.flush()
    conn.send(None)
    proc.join(5)
    return 0


if __name__ == "__main__":
    sys.exit(main())
