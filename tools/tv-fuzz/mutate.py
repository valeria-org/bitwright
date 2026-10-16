# Mutates one thing in each function of an optimized module: a constant, an operation, a
# predicate, a flag dropped or added, an attribute added (to a parameter, the return value or
# a call's argument), or the entries of a phi swapped. The mutants stay valid LLVM IR; many
# of them no longer refine the source, which is what bitwright must find.
import random, re, sys
seed = int(sys.argv[1])
rnd = random.Random(seed)
text = open(sys.argv[2]).read()
funcs = re.split(r'(?m)^(?=define )', text)
out = []
log = []

FLAGS = {"add": ["nuw", "nsw"], "sub": ["nuw", "nsw"], "mul": ["nuw", "nsw"], "shl": ["nuw", "nsw"],
         "udiv": ["exact"], "sdiv": ["exact"], "lshr": ["exact"], "ashr": ["exact"],
         "or": ["disjoint"], "icmp": ["samesign"], "zext": ["nneg"], "trunc": ["nuw", "nsw"]}

def width_of(line):
    m = re.search(r'\bi(\d+)\b', line)
    return int(m.group(1)) if m else 8

def small_range(w):
    lo = rnd.choice([0, 0, 1, -1, 2])
    hi = lo + rnd.choice([1, 2, 10, 100, (1 << (w - 1))])
    hi = min(hi, (1 << (w - 1)) - 1) if hi > 0 else hi
    if hi == lo:
        hi = lo + 1
    return f"range(i{w} {lo}, {hi})"

def line_mutations(l):
    """The mutations of one instruction (or `ret`) line: (kind, mutated line)."""
    head, sep, tail = l.partition("=") if re.match(r'\s+%[\w.]+ = ', l) else ("", "", l)
    ms = []
    nums = list(re.finditer(r'(?<=[ ,(\[])-?\d+(?=[ ,)\]]|$)', tail))
    nums = [n for n in nums if not re.search(r'range\(i\d+ [^)]*$', tail[:n.start()])]
    if nums:
        n = rnd.choice(nums)
        v = int(n.group()) + rnd.choice([-1, 1])
        t = tail[:n.start()] + str(v) + tail[n.end():]
        ms.append(("const", head + sep + t))
    op = (tail.split() or [""])[0]
    if op in FLAGS:
        missing = [f for f in FLAGS[op] if not re.search(r'\b' + f + r'\b', tail)]
        if missing:
            f = rnd.choice(missing)
            ms.append(("addflag", head + sep + re.sub(r'\b' + op + r'\b', f"{op} {f}", tail, count=1)))
    if re.search(r'\b(nuw|nsw|exact|disjoint|samesign|nneg) ', tail):
        ms.append(("dropflag", head + sep + re.sub(r'\b(nuw|nsw|exact|disjoint|samesign|nneg) ', '', tail, count=1)))
    m = re.search(r'icmp (?:samesign )?(eq|ne|ugt|uge|ult|ule|sgt|sge|slt|sle)', tail)
    if m:
        preds = ["eq","ne","ugt","uge","ult","ule","sgt","sge","slt","sle"]
        new = rnd.choice([p for p in preds if p != m.group(1)])
        ms.append(("pred", head + sep + tail[:m.start(1)] + new + tail[m.end(1):]))
    if op in ("add", "sub", "and", "or", "xor") and "disjoint" not in tail:
        ops = ["add","sub","and","or","xor"]
        new = rnd.choice([o for o in ops if o != op])
        flagless = re.sub(r'\b(nuw|nsw|disjoint) ', '', tail)
        ms.append(("op", head + sep + flagless.replace(op, new, 1)))
    if re.search(r'\bcall\b', tail):
        args = re.search(r'\((.*)\)\s*$', tail)
        if args and "noundef" not in args.group(1):
            first = re.match(r'\s*(i\d+) ', args.group(1))
            if first:
                a = args.start(1) + first.end(1)
                ms.append(("call_noundef", head + sep + tail[:a] + " noundef" + tail[a:]))
        if "noundef" not in tail.split("@")[0]:
            ms.append(("call_ret_noundef", head + sep + tail.replace("call ", "call noundef ", 1)))
    m = re.match(r'(\s*phi i\d+ )\[ ([^,]+), (%[\w.]+) \], \[ ([^,]+), (%[\w.]+) \]\s*$', tail)
    if m and m.group(2) != m.group(4):
        ms.append(("phi_swap", head + sep + f"{m.group(1)}[ {m.group(4)}, {m.group(3)} ], [ {m.group(2)}, {m.group(5)} ]"))
    return ms

def header_mutations(h):
    """Attributes added to the define line: a parameter's `noundef` or `range`, a return range."""
    ms = []
    params = list(re.finditer(r'(i(\d+))((?: [a-z_]+(?:\([^)]*\))?)*) (%[\w.]+)(?=[,)])', h))
    if params:
        p = rnd.choice(params)
        if "noundef" not in p.group(3):
            ms.append(("param_noundef", h[:p.end(1)] + " noundef" + h[p.end(1):]))
        if "range" not in p.group(3):
            ms.append(("param_range", h[:p.end(1)] + " " + small_range(int(p.group(2))) + h[p.end(1):]))
    m = re.match(r'(define [^@]*?)(range\([^)]*\) )?(i(\d+)) @', h)
    if m and not m.group(2):
        ms.append(("ret_range", h[:m.start(3)] + small_range(int(m.group(4))) + " " + h[m.start(3):]))
    return ms

for f in funcs:
    if not f.startswith("define"):
        out.append(f); continue
    lines = f.split("\n")
    choices = []
    for i, l in enumerate(lines):
        if i == 0:
            choices += [(i, k, m) for (k, m) in header_mutations(l)]
        elif re.match(r'\s+%[\w.]+ = ', l) or re.match(r'\s+ret ', l) or re.match(r'\s+(tail )?call ', l):
            choices += [(i, k, m) for (k, m) in line_mutations(l)]
    if not choices:
        out.append(f); continue
    i, k, m = rnd.choice(choices)
    name = re.match(r'define[^@]*@(\w+)', f).group(1)
    log.append(f"{name}\t{k}\t{lines[i].strip()}  -->  {m.strip()}")
    lines[i] = m
    out.append("\n".join(lines))
open(sys.argv[3], "w").write("".join(out))
open(sys.argv[4], "w").write("\n".join(log) + "\n")
