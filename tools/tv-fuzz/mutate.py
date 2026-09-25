import random, re, sys
seed = int(sys.argv[1])
rnd = random.Random(seed)
text = open(sys.argv[2]).read()
funcs = re.split(r'(?m)^(?=define )', text)
out = []
log = []
for f in funcs:
    if not f.startswith("define"):
        out.append(f); continue
    lines = f.split("\n")
    idx = [i for i,l in enumerate(lines) if re.match(r'\s+%[\w.]+ = ', l) or re.match(r'\s+ret ', l)]
    if not idx:
        out.append(f); continue
    i = rnd.choice(idx)
    l = lines[i]
    kinds = []
    if re.search(r'(?<=[ ,(])-?\d+(?=[ ,)]|$)', l.split('=',1)[-1]): kinds.append("const")
    if re.search(r'\b(add|sub|mul|shl)\b', l) and 'nsw' not in l: kinds.append("nsw")
    if re.search(r'\b(nuw|nsw|exact|disjoint|samesign|nneg)\b', l): kinds.append("dropflag")
    if re.search(r'icmp (eq|ne|ugt|uge|ult|ule|sgt|sge|slt|sle)', l): kinds.append("pred")
    if re.search(r'\b(add|sub|and|or|xor)\b', l): kinds.append("op")
    if not kinds:
        out.append(f); continue
    k = rnd.choice(kinds)
    m = l
    if k == "const":
        head, _, tail = l.partition('=') if '=' in l else ('', '', l)
        nums = list(re.finditer(r'(?<=[ ,(])-?\d+(?=[ ,)]|$)', tail))
        if nums:
            n = rnd.choice(nums)
            v = int(n.group()) + rnd.choice([-1, 1])
            tail = tail[:n.start()] + str(v) + tail[n.end():]
            m = (head + '=' + tail) if head else tail
    elif k == "nsw":
        m = re.sub(r'\b(add|sub|mul|shl)\b', r'\1 nsw', l, count=1)
    elif k == "dropflag":
        m = re.sub(r'\b(nuw|nsw|exact|disjoint|samesign|nneg) ', '', l, count=1)
    elif k == "pred":
        preds = ["eq","ne","ugt","uge","ult","ule","sgt","sge","slt","sle"]
        m = re.sub(r'icmp (\w+)', lambda mm: "icmp " + rnd.choice([p for p in preds if p != mm.group(1)]), l, count=1)
    elif k == "op":
        ops = ["add","sub","and","or","xor"]
        m = re.sub(r'\b(add|sub|and|or|xor)\b', lambda mm: rnd.choice([o for o in ops if o != mm.group(1)]), l, count=1)
    lines[i] = m
    name = re.match(r'define[^@]*@(\w+)', f).group(1)
    log.append(f"{name}\t{k}\t{l.strip()}  -->  {m.strip()}")
    out.append("\n".join(lines))
open(sys.argv[3], "w").write("".join(out))
open(sys.argv[4], "w").write("\n".join(log) + "\n")
