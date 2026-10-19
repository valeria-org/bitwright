"""Markdown rows of the proposal's sweep tables: per option, roots whose result changed against
the baseline (and how many of them got larger) by fuel; and random DAGs' instructions by fuel.

    sweep_tables.py BASE.tsv LABEL=FILE...
"""
import sys

FUELS = ['default', '2^18', '2^16', '2^14', '2^12', '2^10', '2^8']


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


def dags(tot, f):
    return sum(float(kv['instr']) for (c, g), kv in tot.items() if g == f and 'dags' in c) / 1e9


def mba(tot, f):
    return sum(float(kv['instr']) for (c, g), kv in tot.items() if g == f and 'dags' not in c) / 1e9


base_roots, base_tot = load(sys.argv[1])
opts = [a.split('=', 1) for a in sys.argv[2:]]
loaded = [(label, load(path)) for label, path in opts]
for label, (roots, tot) in loaded:
    cells = []
    for f in FUELS:
        ch = [k for k in roots if k[1] == f and roots[k][1] != base_roots[k][1]]
        larger = sum(1 for k in ch if roots[k][0] > base_roots[k][0])
        cells.append('0' if not ch else f'{len(ch)} ({larger})')
    print(f'| {label} | ' + ' | '.join(cells) + ' |')
print()
print('| today | ' + ' | '.join(f'{dags(base_tot, f):.1f} G' for f in FUELS[:6]) + ' |')
for label, (roots, tot) in loaded:
    print(f'| {label} | ' + ' | '.join(f'{dags(tot, f):.1f} G' for f in FUELS[:6]) + ' |')
print()
print('MBA corpora instructions at 2^18 / 2^14 / 2^10:')
print(f'  today {mba(base_tot, "2^18"):.2f} / {mba(base_tot, "2^14"):.2f} / {mba(base_tot, "2^10"):.2f}')
for label, (roots, tot) in loaded:
    print(f'  {label} {mba(tot, "2^18"):.2f} / {mba(tot, "2^14"):.2f} / {mba(tot, "2^10"):.2f}')
