"""Per dataset of a compare BW_CALLS dump (with R lines): cases, cases that asked the solver,
the solver's share of the engine's instructions and CPU time, and per-case totals.

    cobra_share.py FILE"""
import sys
from collections import defaultdict

def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, max(0, int(round(p * (len(xs) - 1)))))] if xs else 0

runs = defaultdict(dict)
calls = defaultdict(lambda: defaultdict(lambda: [0, 0, 0, 0]))
for line in open(sys.argv[1]):
    p = line.rstrip('\n').split('\t')
    if p[0] == 'R':
        kv = dict(x.split('=', 1) for x in p[3:])
        runs[p[1]][p[2]] = (int(kv['instr']), int(kv['cpu']))
    elif p[0] == 'C':
        c = calls[p[1]][p[2]]
        c[0] += int(p[10]); c[1] += int(p[12]); c[2] += int(p[7]); c[3] += 1
tot = [0, 0, 0, 0, 0]
print(f'{"dataset":<28}{"cases":>7}{"instr":>10}{"solver":>8}{"cpu s":>8}{"solver":>8}{"steps/case p50":>15}{"p99":>9}{"max":>9}{"instr/case max":>15}')
for ds, rs in sorted(runs.items()):
    ri = sum(r[0] for r in rs.values()); rc = sum(r[1] for r in rs.values())
    si = sum(c[0] for c in calls[ds].values()); sc = sum(c[1] for c in calls[ds].values())
    steps = [calls[ds][k][2] for k in rs]
    print(f'{ds:<28}{len(rs):>7}{ri/1e9:>9.2f}G{100*si/max(ri,1):>7.1f}%{rc/1e9:>8.2f}{100*sc/max(rc,1):>7.1f}%'
          f'{q(steps,.5):>15}{q(steps,.99):>9}{max(steps):>9}{max(r[0] for r in rs.values())/1e6:>14.1f}M')
    tot[0] += len(rs); tot[1] += ri; tot[2] += si; tot[3] += rc; tot[4] += sc
print(f'{"all":<28}{tot[0]:>7}{tot[1]/1e9:>9.2f}G{100*tot[2]/tot[1]:>7.1f}%{tot[3]/1e9:>8.2f}{100*tot[4]/tot[3]:>7.1f}%')
