import random, sys
seed = int(sys.argv[1]); n = int(sys.argv[2])
rnd = random.Random(seed)
FMF = ["nnan", "ninf", "nsz", "arcp", "contract", "reassoc", "afn"]
FPRED = ["oeq","ogt","oge","olt","ole","one","ord","ueq","ugt","uge","ult","ule","une","uno"]
out = []
for f in range(n):
    ty = rnd.choice(["float", "double", "half"])
    vals = ["%a", "%b"]
    bools = []
    body = []
    k = 0
    def flags():
        return " ".join(x for x in FMF if rnd.random() < 0.15)
    def opnd():
        if rnd.random() < 0.3:
            return rnd.choice(["0.0", "-0.0", "1.0", "-1.0", "2.0", "0.5", "0x7FF0000000000000", "0xFFF0000000000000", "0x7FF8000000000000"]) if ty != "half" else rnd.choice(["0.0", "-0.0", "1.0", "-1.0", "2.0", "0.5", "0xH7C00", "0xHFC00", "0xH7E00"])
        return rnd.choice(vals)
    for _ in range(rnd.randint(1, 4)):
        k += 1
        r = f"%t{k}"
        kind = rnd.random()
        if kind < 0.5:
            op = rnd.choice(["fadd", "fsub", "fmul", "fdiv"])
            body.append(f"{r} = {op} {flags()} {ty} {opnd()}, {opnd()}".replace("  ", " "))
            vals.append(r)
        elif kind < 0.65:
            body.append(f"{r} = fneg {flags()} {ty} {opnd()}".replace("  ", " "))
            vals.append(r)
        elif kind < 0.85:
            body.append(f"{r} = fcmp {flags()} {rnd.choice(FPRED)} {ty} {opnd()}, {opnd()}".replace("  ", " "))
            bools.append(r)
        elif bools:
            body.append(f"{r} = select {flags()} i1 {rnd.choice(bools)}, {ty} {opnd()}, {ty} {opnd()}".replace("  ", " "))
            vals.append(r)
        else:
            fn = rnd.choice(["fabs", "sqrt", "minnum", "maxnum", "minimum", "maximum", "floor", "ceil", "trunc", "copysign"])
            suffix = {"float": "f32", "double": "f64", "half": "f16"}[ty]
            nargs = 2 if fn in ("minnum","maxnum","minimum","maximum","copysign") else 1
            args = ", ".join(f"{ty} {opnd()}" for _ in range(nargs))
            body.append(f"{r} = call {flags()} {ty} @llvm.{fn}.{suffix}({args})".replace("  ", " "))
            vals.append(r)
    last = vals[-1]
    if last in ("%a", "%b"):
        body.append(f"%t{k+1} = fadd {ty} %a, %b"); last = f"%t{k+1}"
    out.append(f"define {ty} @f{f}({ty} %a, {ty} %b) {{\n" + "\n".join("  "+l.strip() for l in body) + f"\n  ret {ty} {last}\n}}\n")
print("\n".join(out))
