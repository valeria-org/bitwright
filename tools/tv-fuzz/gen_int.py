import random, sys
seed = int(sys.argv[1]); n = int(sys.argv[2])
rnd = random.Random(seed)
BIN = [("add",["nuw","nsw"]),("sub",["nuw","nsw"]),("mul",["nuw","nsw"]),("udiv",["exact"]),("sdiv",["exact"]),
       ("urem",[]),("srem",[]),("shl",["nuw","nsw"]),("lshr",["exact"]),("ashr",["exact"]),("and",[]),("or",["disjoint"]),("xor",[])]
PRED = ["eq","ne","ugt","uge","ult","ule","sgt","sge","slt","sle"]
out = []
for f in range(n):
    W = rnd.choice([8, 8, 16, 32])
    ty = f"i{W}"
    vals = ["%a", "%b", "%c"]
    bools = []
    body = []
    k = 0
    for _ in range(rnd.randint(2, 6)):
        k += 1
        r = f"%t{k}"
        kind = rnd.random()
        def opnd():
            if rnd.random() < 0.25:
                return str(rnd.choice([0, 1, -1, 2, 3, 7, 8, W-1, 255 if W>8 else 127, -128 if W>=8 else 1]))
            return rnd.choice(vals)
        if kind < 0.6:
            op, fl = rnd.choice(BIN)
            if op in ("udiv","sdiv","urem","srem") and rnd.random() < 0.7:
                y = str(rnd.choice([1,2,3,4,7,8,-1,-2]))
            else:
                y = opnd()
            flags = " ".join(x for x in fl if rnd.random() < 0.3)
            if op in ("shl","lshr","ashr") and rnd.random() < 0.7:
                y = str(rnd.randint(0, W-1))
            body.append(f"  {r} = {op} {flags} {ty} {opnd()}, {y}".replace("  ", " ").replace("= ", "= ").rstrip())
            vals.append(r)
        elif kind < 0.8:
            p = rnd.choice(PRED)
            body.append(f"  {r} = icmp {p} {ty} {opnd()}, {opnd()}")
            bools.append(r)
        elif bools:
            c = rnd.choice(bools)
            body.append(f"  {r} = select i1 {c}, {ty} {opnd()}, {ty} {opnd()}")
            vals.append(r)
        else:
            fn = rnd.choice(["umin","umax","smin","smax"])
            body.append(f"  {r} = call {ty} @llvm.{fn}.{ty}({ty} {opnd()}, {ty} {opnd()})")
            vals.append(r)
    last = vals[-1] if vals[-1] not in ("%a","%b","%c") else None
    if last is None:
        body.append(f"  %t{k+1} = add {ty} %a, %b"); last = f"%t{k+1}"
    out.append(f"define {ty} @f{f}({ty} %a, {ty} %b, {ty} %c) {{\n" + "\n".join("  "+l.strip() for l in body) + f"\n  ret {ty} {last}\n}}\n")
print("\n".join(out))
