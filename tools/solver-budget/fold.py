"""Folds `perf script` output (frame-pointer call graphs) of a bench probe run: samples under
the solver, attributed to the solver's own phases (the outermost nf:: frames below `solve`) and,
within them, to certificate work (certify::) or the rest.

    perf script -i DATA | fold.py [DEPTH]
"""
import re
import sys
from collections import Counter

depth = int(sys.argv[1]) if len(sys.argv) > 1 else 3
total = 0
under = Counter()
leaf = Counter()
cur = []


def short(sym):
    m = re.match(r'<bitwright::mba::(?:[a-z_]+::)*([A-Z][A-Za-z]*)(?:<[^>]*>)?(?: as [^>]*)?>::([a-z_]+)', sym)
    if m:
        return f'{m.group(1)}::{m.group(2)}'
    sym = re.sub(r'<[^<>]*>', '', sym)
    sym = re.sub(r'<[^<>]*>', '', sym)
    sym = sym.replace('bitwright::mba::', '').replace('bitwright::', '')
    return re.sub(r"\+0x[0-9a-f]+$", "", sym.split("(")[0].strip())


def flush():
    global total
    if not cur:
        return
    total += 1
    frames = cur[::-1]  # outermost first
    names = [f for f in frames]
    try:
        i = next(k for k, f in enumerate(names) if 'NormalFormSolver' in f and 'solve' in f)
    except StopIteration:
        under['(not in the solver)'] += 1
        return
    path = []
    for f in names[i + 1:]:
        s = short(f)
        if not s or s in path:
            continue
        if s.startswith(('nf::', 'certify::', 'Compose::', 'Render::', 'Program::')):
            path.append(s)
        if len(path) >= depth:
            break
    under[' > '.join(path) or '(solve itself)'] += 1
    leaf[short(names[-1])] += 1


for line in sys.stdin:
    line = line.rstrip('\n')
    if not line.strip():
        flush()
        cur = []
        continue
    if line[0] not in ' \t':
        continue
    parts = line.strip().split(None, 1)
    if len(parts) == 2:
        cur.append(parts[1].rsplit(' (', 1)[0])
flush()
print(f'{total} samples')
for k, v in under.most_common(40):
    print(f'{100 * v / total:6.1f}%  {k}')
print()
for k, v in leaf.most_common(15):
    print(f'{100 * v / total:6.1f}%  leaf {k}')
