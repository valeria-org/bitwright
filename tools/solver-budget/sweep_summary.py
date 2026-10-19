"""Per option, against the baseline sweep: roots whose result changed (and how many got larger
or smaller), by corpus group and fuel; and instructions by fuel (random DAGs, MBA corpora).

    sweep_summary.py BASE.tsv OTHER.tsv...
"""
import sys
from collections import defaultdict

FUELS = ['default', '2^18', '2^16', '2^14', '2^12', '2^10', '2^8']


def group(corpus):
    if 'dags' in corpus:
        return 'dags'
    if 'nonlinear' in corpus:
        return 'nonlinear'
    if corpus.startswith('bench'):
        return 'bench'
    return 'linear'


def load(path):
    roots, totals = {}, {}
    for line in open(path):
        if line.startswith('#'):
            continue
        p = line.rstrip('\n').split('\t')
        if p[0] == 'R':
            roots[(p[1], p[2], p[3])] = (int(p[4]), p[6])
        elif p[0] == 'T':
            totals[(p[1], p[2])] = dict(x.split('=', 1) for x in p[3:])
    return roots, totals


def instr(totals, fuel, pred):
    return sum(float(kv['instr']) for (c, f), kv in totals.items() if f == fuel and pred(c)) / 1e9


base_roots, base_tot = load(sys.argv[1])
print(f'baseline {sys.argv[1]}: instructions (G) by fuel, random DAGs / MBA corpora')
print('  ' + '  '.join(f'{f}: {instr(base_tot, f, lambda c: "dags" in c):.1f}/{instr(base_tot, f, lambda c: "dags" not in c):.2f}' for f in FUELS))
for path in sys.argv[2:]:
    roots, tot = load(path)
    print(f'=== {path.split("/")[-1]}')
    for f in FUELS:
        ch = defaultdict(lambda: [0, 0, 0])
        for k, (size, text) in roots.items():
            if k[1] != f:
                continue
            b = base_roots[k]
            if text != b[1]:
                g = ch[group(k[0])]
                g[0] += 1
                g[1] += size > b[0]
                g[2] += size < b[0]
        n = sum(v[0] for v in ch.values())
        detail = ', '.join(f'{g} {v[0]} (+{v[1]}/-{v[2]})' for g, v in sorted(ch.items()))
        bi, oi = instr(base_tot, f, lambda c: 'dags' in c), instr(tot, f, lambda c: 'dags' in c)
        bm, om = instr(base_tot, f, lambda c: 'dags' not in c), instr(tot, f, lambda c: 'dags' not in c)
        print(f'  {f:>8}: {n:>4} changed  [{detail}]  dags {bi:.1f} -> {oi:.1f} G, mba {bm:.2f} -> {om:.2f} G')
