# An independent interpreter (sharing no code with bitwright) for the integer subset of LLVM IR the fuzzer produces: values are
# ints (unsigned, mod 2^w) or POISON; undefined behavior raises UB. freeze of poison picks a
# random value. Each function reads its parameters through its own attributes (`range`
# makes an argument outside it poison, `noundef` makes a poison one undefined behavior), and
# call sites likewise (`noundef` and `range` on arguments and results).
import re, random, sys
POISON = "poison"
class UB(Exception): pass

def split_top(s):
    """Splits at the commas outside parentheses and brackets."""
    parts, depth, cur = [], 0, ""
    for ch in s:
        if ch in "([":
            depth += 1
        elif ch in ")]":
            depth -= 1
        if ch == "," and depth == 0:
            parts.append(cur)
            cur = ""
        else:
            cur += ch
    if cur.strip():
        parts.append(cur)
    return parts

RANGE = r'range\(i(\d+) (-?\d+), (-?\d+)\)'

def ranged(v, rng):
    """`v` through a `range(iW lo, hi)` attribute (a match of RANGE, or None)."""
    if rng is None or v == POISON:
        return v
    rw, lo, hi = int(rng.group(1)), int(rng.group(2)), int(rng.group(3))
    if (v - lo) % (1 << rw) >= (hi - lo) % (1 << rw):
        return POISON
    return v

def parse(text):
    funcs = {}
    for m in re.finditer(r'(?m)^define ([^\n]*?)@(\w+)\(', text):
        head, name = m.group(1), m.group(2)
        # The parameter list, to its matching parenthesis.
        i, depth = m.end(), 1
        while depth:
            depth += {"(": 1, ")": -1}.get(text[i], 0)
            i += 1
        params = text[m.end():i - 1]
        body_start = text.index("{\n", i) + 2
        body_end = re.compile(r'(?m)^\}').search(text, body_start).start()
        body = text[body_start:body_end]
        ps = []
        for p in split_top(params):
            toks = p.split()
            if not toks:
                continue
            ps.append(dict(name=toks[-1], w=int(toks[0][1:]), noundef="noundef" in toks,
                           range=re.search(RANGE, p)))
        rng = re.search(RANGE, head)
        ret_noundef = "noundef" in head.split()
        # An unlabeled entry block takes the next unnamed number (after unnamed parameters).
        entry = str(sum(1 for p in ps if re.fullmatch(r'%\d+', p["name"])))
        blocks = {}; order = []; cur = entry; blocks[cur] = []; order.append(cur)
        first = True
        pending = None
        for line in body.split("\n"):
            line = line.split(";")[0].strip()
            if not line: continue
            # A statement over several lines (a switch's cases).
            if pending is not None:
                pending += " " + line
                if pending.count("[") > pending.count("]"):
                    continue
                line, pending = pending, None
            elif line.count("[") > line.count("]"):
                pending = line
                continue
            lm = re.match(r'^([\w.]+):$', line)
            if lm:
                if first and not blocks[entry]:
                    del blocks[entry]; order.remove(entry)
                cur = lm.group(1); blocks[cur] = []; order.append(cur); first = False
                continue
            first = False
            blocks[cur].append(line)
        funcs[name] = dict(params=ps, blocks=blocks, order=order, range=rng, ret_noundef=ret_noundef)
    return funcs

def sx(v, w): return v - (1 << w) if v >> (w - 1) & 1 else v
def mask(w): return (1 << w) - 1

def run(f, args, rnd, frozen=None, trace=None, chosen=None):
    """`frozen`: what freezing each poison parameter gives (by name; others random);
    `chosen`: what each freeze gives, by its register (a counterexample's choices);
    `trace["freeze"]` is set when a poison value is frozen."""
    frozen = frozen or {}
    chosen = chosen or {}
    trace = trace if trace is not None else {}
    env = {}
    for p, a in zip(f["params"], args):
        a = ranged(a, p["range"])
        if a == POISON and p["noundef"]: raise UB()
        env[p["name"]] = a
    def val(tok, w):
        tok = tok.strip()
        if tok.startswith("%"): return env[tok]
        if tok == "true": return 1
        if tok == "false": return 0
        if tok == "poison": return POISON
        return int(tok) & mask(w)
    block = f["order"][0]; prev = None
    while True:
        lines = f["blocks"][block]
        # Phis read their values at once, on the edge taken.
        phis = {}
        for line in lines:
            m = re.match(r'^(%[\w.]+) = phi i(\d+) (.*)$', line)
            if not m: continue
            w = int(m.group(2))
            for inc in re.finditer(r'\[\s*([^,\]]+),\s*%([\w.]+)\s*\]', m.group(3)):
                if inc.group(2) == prev:
                    phis[m.group(1)] = val(inc.group(1), w)
        env.update(phis)
        for line in lines:
            m = re.match(r'^(%[\w.]+) = (.*)$', line)
            if m: dst, rhs = m.group(1), m.group(2)
            else: dst, rhs = None, line
            rhs = re.sub(r"^(tail|musttail|notail) call", "call", rhs); op = rhs.split()[0]
            if op == "phi":
                continue
            if op == "ret":
                t = rhs.split()[1]; w = int(t[1:])
                v = ranged(val(rhs.split(None, 2)[2], w), f["range"])
                if v == POISON and f["ret_noundef"]: raise UB()
                return v
            if op == "unreachable":
                raise UB()
            if op == "br":
                if rhs.startswith("br label"):
                    prev, block = block, rhs.split("%")[1]; break
                mm = re.match(r'br i1 ([^,]+), label %([\w.]+), label %([\w.]+)', rhs)
                c = val(mm.group(1), 1)
                if c == POISON: raise UB()
                prev, block = block, (mm.group(2) if c else mm.group(3)); break
            if op == "switch":
                mm = re.match(r'switch i(\d+) ([^,]+), label %([\w.]+) \[(.*)\]', rhs)
                w = int(mm.group(1)); c = val(mm.group(2), w)
                if c == POISON: raise UB()
                to = mm.group(3)
                for case in re.finditer(r'i\d+ (-?\d+), label %([\w.]+)', mm.group(4)):
                    if int(case.group(1)) & mask(w) == c:
                        to = case.group(2); break
                prev, block = block, to; break
            if rhs.startswith("freeze"):
                toks = rhs.split()
                w, x = int(toks[1][1:]), toks[2]
                v = val(x, w)
                if v == POISON:
                    trace["freeze"] = True
                    if dst in chosen:
                        v = chosen[dst] & mask(w)
                    elif x in frozen:
                        v = frozen[x] & mask(w)
                    else:
                        v = rnd.randrange(1 << w)
                env[dst] = v
                continue
            env[dst] = evaluate(rhs, val, env, rnd, prev)
        else:
            raise Exception("fell off a block")

def call(rhs, val):
    m = re.match(r'call (.*?)i(\d+) @llvm\.([\w.]+?)\.i\d+\((.*)\)\s*$', rhs)
    attrs, w, fn = m.group(1), int(m.group(2)), m.group(3)
    vals = []
    for a in split_top(m.group(4)):
        toks = a.split()
        v = ranged(val(toks[-1], int(toks[0][1:])), re.search(RANGE, a))
        if v == POISON and "noundef" in toks: raise UB()
        vals.append(v)
    r = intrinsic(fn, w, vals)
    r = ranged(r, re.search(RANGE, attrs))
    if r == POISON and "noundef" in attrs.split(): raise UB()
    return r

def intrinsic(fn, w, vals):
    if fn in ("umin","umax","smin","smax"):
        a, b = vals
        if a == POISON or b == POISON: return POISON
        if fn == "umin": return min(a, b)
        if fn == "umax": return max(a, b)
        if fn == "smin": return a if sx(a,w) <= sx(b,w) else b
        return a if sx(a,w) >= sx(b,w) else b
    if fn == "abs":
        a, flag = vals
        if a == POISON or flag == POISON: return POISON
        if flag and a == 1 << (w-1): return POISON
        return abs(sx(a,w)) & mask(w)
    if fn == "ctpop":
        return POISON if vals[0] == POISON else bin(vals[0]).count("1")
    if fn in ("ctlz","cttz"):
        a, flag = vals
        if a == POISON or flag == POISON: return POISON
        if a == 0: return POISON if flag else w
        if fn == "ctlz": return w - a.bit_length()
        return (a & -a).bit_length() - 1
    raise Exception("unknown call " + fn)

def evaluate(rhs, val, env, rnd, prev):
    if rhs.startswith("call"):
        return call(rhs, val)
    toks = rhs.replace(",", " , ").split()
    op = toks[0]
    flags = set()
    i = 1
    while toks[i] in ("nuw", "nsw", "exact", "disjoint", "samesign", "nneg"):
        flags.add(toks[i]); i += 1
    if op in ("add","sub","mul","udiv","sdiv","urem","srem","shl","lshr","ashr","and","or","xor"):
        w = int(toks[i][1:]); rest = " ".join(toks[i+1:]).split(" , ")
        a, b = val(rest[0], w), val(rest[1], w)
        if op in ("udiv","urem","sdiv","srem"):
            if b == POISON or b == 0: raise UB()
            if op in ("sdiv","srem") and sx(b,w) == -1 and (a == POISON or sx(a,w) == -(1 << (w-1))): raise UB()
        if a == POISON or b == POISON: return POISON
        M = mask(w)
        if op == "add":
            r = (a + b) & M
            if "nuw" in flags and a + b > M: return POISON
            if "nsw" in flags and not (-(1<<(w-1)) <= sx(a,w)+sx(b,w) < (1<<(w-1))): return POISON
            return r
        if op == "sub":
            r = (a - b) & M
            if "nuw" in flags and a < b: return POISON
            if "nsw" in flags and not (-(1<<(w-1)) <= sx(a,w)-sx(b,w) < (1<<(w-1))): return POISON
            return r
        if op == "mul":
            r = (a * b) & M
            if "nuw" in flags and a * b > M: return POISON
            if "nsw" in flags and not (-(1<<(w-1)) <= sx(a,w)*sx(b,w) < (1<<(w-1))): return POISON
            return r
        if op == "udiv":
            if "exact" in flags and a % b: return POISON
            return a // b
        if op == "urem": return a % b
        if op in ("sdiv", "srem"):
            x, y = sx(a,w), sx(b,w)
            q = abs(x) // abs(y) * (1 if (x >= 0) == (y >= 0) else -1)
            if op == "sdiv":
                if "exact" in flags and q * y != x: return POISON
                return q & M
            return (x - q * y) & M
        if op in ("shl","lshr","ashr"):
            if b >= w: return POISON
            if op == "shl":
                r = (a << b) & M
                if "nuw" in flags and (r >> b) != a: return POISON
                if "nsw" in flags and (sx(r,w) >> b) & M != a: return POISON
                return r
            if op == "lshr":
                r = a >> b
            else:
                r = (sx(a,w) >> b) & M
            if "exact" in flags and a & ((1 << b) - 1): return POISON
            return r
        if op == "and": return a & b
        if op == "xor": return a ^ b
        if op == "or":
            if "disjoint" in flags and a & b: return POISON
            return a | b
    if op == "icmp":
        pred = toks[i]; w = int(toks[i+1][1:]); rest = " ".join(toks[i+2:]).split(" , ")
        a, b = val(rest[0], w), val(rest[1], w)
        if a == POISON or b == POISON: return POISON
        if "samesign" in flags and (a >> (w-1)) != (b >> (w-1)): return POISON
        sa, sb = sx(a,w), sx(b,w)
        return int({"eq":a==b,"ne":a!=b,"ugt":a>b,"uge":a>=b,"ult":a<b,"ule":a<=b,"sgt":sa>sb,"sge":sa>=sb,"slt":sa<sb,"sle":sa<=sb}[pred])
    if op == "select":
        # select i1 c , ty a , ty b
        parts = " ".join(toks[1:]).split(" , ")
        c = val(parts[0].split()[1], 1)
        w = int(parts[1].split()[0][1:])
        a, b = val(parts[1].split()[1], w), val(parts[2].split()[1], w)
        if c == POISON: return POISON
        return a if c else b
    if op == "freeze":
        w = int(toks[1][1:]); a = val(toks[2], w)
        return rnd.randrange(1 << w) if a == POISON else a
    if op in ("zext","sext","trunc"):
        w = int(toks[i][1:]); a = val(toks[i+1], w); to = int(toks[i+3][1:])
        if a == POISON: return POISON
        if op == "zext":
            if "nneg" in flags and a >> (w-1): return POISON
            return a
        if op == "sext": return sx(a, w) & mask(to)
        r = a & mask(to)
        if "nuw" in flags and r != a: return POISON
        if "nsw" in flags and sx(r, to) != sx(a, w): return POISON
        return r
    raise Exception("unknown op " + op)

def behaviors(f, args, rnd, frozen=None, trace=None, chosen=None):
    try:
        return run(f, args, rnd, frozen, trace, chosen)
    except UB:
        return "UB"

def refines(s, t):
    if s == "UB": return True
    if t == "UB": return False
    if s == POISON: return True
    if t == POISON: return False
    return s == t

def random_args(f, rnd):
    """Arguments a caller may pass: never poison where the source declares `noundef`."""
    args = []
    for p in f["params"]:
        w = p["w"]
        r = rnd.random()
        if r < 0.1 and not p["noundef"]: args.append(POISON)
        elif r < 0.5: args.append(rnd.choice([0, 1, mask(w), 1 << (w-1), (1 << (w-1)) - 1, 2, 3, 7, 8]) & mask(w))
        else: args.append(rnd.randrange(1 << w))
    return args

if __name__ == "__main__":
    src = parse(open(sys.argv[1]).read()); tgt = parse(open(sys.argv[2]).read())
    names = sys.argv[3].split(",") if len(sys.argv) > 3 and sys.argv[3] else list(src)
    samples = int(sys.argv[4]) if len(sys.argv) > 4 else 3000
    rnd = random.Random(1)
    for name in names:
        if name not in tgt: continue
        f, g = src[name], tgt[name]
        bad = None
        for k in range(samples):
            args = random_args(f, rnd)
            try:
                s = behaviors(f, args, rnd); t = behaviors(g, args, rnd)
            except Exception as e:
                bad = f"error {e}"; break
            if not refines(s, t):
                bad = f"args={args} src={s} tgt={t}"; break
        print(f"{name}\t{'OK' if bad is None else 'MISMATCH ' + bad}")
