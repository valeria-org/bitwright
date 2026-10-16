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
    k = 0
    def fresh():
        global k
        k += 1
        return f"%t{k}"
    def opnd(vals):
        if rnd.random() < 0.25:
            return str(rnd.choice([0, 1, -1, 2, 3, 7, 8, W-1, 255 if W>8 else 127, -128 if W>=8 else 1]))
        return rnd.choice(vals)
    def steps(vals, bools, body, count):
        """`count` instructions over `vals` (values) and `bools` (conditions), appended."""
        for _ in range(count):
            r = fresh()
            kind = rnd.random()
            if kind < 0.5:
                op, fl = rnd.choice(BIN)
                if op in ("udiv","sdiv","urem","srem") and rnd.random() < 0.7:
                    y = str(rnd.choice([1,2,3,4,7,8,-1,-2]))
                else:
                    y = opnd(vals)
                flags = " ".join(x for x in fl if rnd.random() < 0.3)
                if op in ("shl","lshr","ashr") and rnd.random() < 0.7:
                    y = str(rnd.randint(0, W-1))
                body.append(f"{r} = {op} {flags} {ty} {opnd(vals)}, {y}".replace("  ", " "))
                vals.append(r)
            elif kind < 0.68:
                p = rnd.choice(PRED)
                body.append(f"{r} = icmp {p} {ty} {opnd(vals)}, {opnd(vals)}")
                bools.append(r)
            elif kind < 0.8 and bools:
                c = rnd.choice(bools)
                body.append(f"{r} = select i1 {c}, {ty} {opnd(vals)}, {ty} {opnd(vals)}")
                vals.append(r)
            elif kind < 0.86:
                body.append(f"{r} = freeze {ty} {rnd.choice(vals)}")
                vals.append(r)
            elif kind < 0.92:
                body.append(f"{r} = call {ty} @llvm.ctpop.{ty}({ty} {rnd.choice(vals)})")
                vals.append(r)
            else:
                fn = rnd.choice(["umin","umax","smin","smax"])
                body.append(f"{r} = call {ty} @llvm.{fn}.{ty}({ty} {opnd(vals)}, {ty} {opnd(vals)})")
                vals.append(r)
    vals = ["%a", "%b", "%c"]
    bools = []
    lines = []
    steps(vals, bools, lines, rnd.randint(1, 4))
    if rnd.random() < 0.5:
        # A diamond: each arm computes a value, a phi joins them.
        if not bools:
            c = fresh()
            lines.append(f"{c} = icmp {rnd.choice(PRED)} {ty} {opnd(vals)}, {opnd(vals)}")
            bools.append(c)
        cond = rnd.choice(bools)
        lines.append(f"br i1 {cond}, label %then, label %else")
        arms = []
        for label in ("then", "else"):
            lines.append(f"{label}:")
            avals, abools = list(vals), list(bools)
            steps(avals, abools, lines, rnd.randint(1, 3))
            # The arm's value: its last one, or one from before the diamond.
            arms.append(avals[-1] if len(avals) > len(vals) else rnd.choice(vals))
            lines.append("br label %join")
        lines.append("join:")
        p = fresh()
        lines.append(f"{p} = phi {ty} [ {arms[0]}, %then ], [ {arms[1]}, %else ]")
        vals.append(p)
        steps(vals, bools, lines, rnd.randint(0, 2))
    last = vals[-1] if vals[-1] not in ("%a","%b","%c") else None
    if last is None:
        r = fresh()
        lines.append(f"{r} = add {ty} %a, %b"); last = r
    lines.append(f"ret {ty} {last}")
    body = "\n".join(l if l.endswith(":") else "  " + l.strip() for l in lines)
    out.append(f"define {ty} @f{f}({ty} %a, {ty} %b, {ty} %c) {{\n{body}\n}}\n")
print("\n".join(out))
