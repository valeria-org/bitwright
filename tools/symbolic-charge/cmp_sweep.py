"""Compares --symbolic-sweep dumps against a baseline dump: per (corpus, fuel), roots whose
result text changed, size sums, pass work, instructions, stopped roots, MBA answers.

    cmp_sweep.py BASE.tsv OTHER.tsv..."""
import sys
from collections import defaultdict

def load(path):
    roots = {}
    totals = {}
    with open(path) as f:
        for line in f:
            if line.startswith('#'):
                continue
            p = line.rstrip('\n').split('\t')
            if p[0] == 'R':
                _, corpus, fuel, idx, size, end, text = p
                roots[(corpus, fuel, idx)] = (int(size), end, text)
            elif p[0] == 'T':
                corpus, fuel = p[1], p[2]
                kv = dict(x.split('=', 1) for x in p[3:])
                totals[(corpus, fuel)] = kv
    return roots, totals

base_path = sys.argv[1]
base_roots, base_tot = load(base_path)
fuels = ['default', '2^18', '2^16', '2^14', '2^12', '2^10', '2^8']
for path in sys.argv[2:]:
    roots, tot = load(path)
    print(f'=== {path.split("/")[-1]} vs {base_path.split("/")[-1]}')
    print(f'{"corpus":<24}{"fuel":>8}{"changed":>9}{"smaller":>8}{"larger":>7}{"size":>14}{"pass":>26}{"Minstr":>22}{"stopped":>12}{"simpl":>10}{"unprov":>10}{"sym":>10}')
    for (corpus, fuel), kv in sorted(tot.items(), key=lambda x: (x[0][0], fuels.index(x[0][1]))):
        b = base_tot[(corpus, fuel)]
        keys = [k for k in roots if k[0] == corpus and k[1] == fuel]
        changed = sum(1 for k in keys if roots[k][2] != base_roots[k][2])
        smaller = sum(1 for k in keys if roots[k][0] < base_roots[k][0])
        larger = sum(1 for k in keys if roots[k][0] > base_roots[k][0])
        def pair(name, scale=1.0, fmt='{:.0f}'):
            x, y = float(b[name]) / scale, float(kv[name]) / scale
            s = fmt.format(x) if x == y else f'{fmt.format(x)}->{fmt.format(y)}'
            return s
        print(f'{corpus:<24}{fuel:>8}{changed:>9}{smaller:>8}{larger:>7}{pair("size"):>14}{pair("pass"):>26}'
              f'{pair("instr", 1e6, "{:.1f}"):>22}{pair("stopped"):>12}{pair("simplified"):>10}{pair("unproved"):>10}{pair("symbolic"):>10}')
    print()
