"""What charging solver steps at a rate R would demand of a run's pass work, from a
--solver-calls dump of today's runs: per corpus, how many runs (inputs) would need more than
Budget::fuel(f)'s pass work (16 f) at each R, if nothing else changed (an estimate: a bound run
stops earlier and spends less).

    demand.py CALLS.tsv [PASS.tsv]

Per-input pass work comes from R lines (--solver-dags) or, for --solver-calls corpora, is not
recorded per input: then only the solver's share is counted."""
import sys
from collections import defaultdict

path = sys.argv[1]
steps = defaultdict(lambda: defaultdict(int))
passw = defaultdict(dict)
for line in open(path):
    p = line.rstrip('\n').split('\t')
    if p[0] == 'C':
        steps[p[1]][p[2]] += int(p[7])
    elif p[0] == 'R':
        kv = dict(x.split('=', 1) for x in p[3:] if '=' in x)
        passw[p[1]][p[2]] = int(kv['pass'])
rates = [1, 2, 4, 8, 16, 32, 64]
fuels = [22, 18, 16, 14, 12]
print(f'{"corpus":<26}{"runs":>6}  ' + ' '.join(f'R={r:<3}' + ''.join(f'{"":1}' for _ in []) for r in rates))
for corpus, runs in steps.items():
    n = len(runs)
    for f in fuels:
        cap = 16 << f
        row = []
        for r in rates:
            over = sum(1 for k, s in runs.items() if s * r + passw[corpus].get(k, 0) > cap)
            row.append(f'{over:>5}')
        print(f'{corpus:<26}{n:>6}  2^{f}: ' + ' '.join(row))
