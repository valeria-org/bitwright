"""Compares bw-nf answer dumps (BW_ANSWERS) and CSVs between configurations of the compare
harness: per configuration against the baseline at the same fuel, answers changed by dataset,
the solved and exact counts, answer sizes and pass work.

    cmp_compare.py DIR BASE TAG1,TAG2,... FUEL...

reads DIR/ans-TAG-FUEL.tsv and DIR/csv-TAG-FUEL.csv. Keyed by (line, input hash), so inputs
repeated at the same line of two datasets count once in "texts changed"; the CSV counts are
per dataset and line."""
import csv
import sys
from collections import Counter, defaultdict

D, BASE = sys.argv[1], sys.argv[2]

def answers(tag):
    out = {}
    with open(f'{D}/ans-{tag}.tsv') as f:
        for line in f:
            ln, h, pass_, end, ans = line.rstrip('\n').split('\t', 4)
            out[(int(ln), h)] = (int(pass_), end, ans)
    return out

def rows(tag):
    out = {}
    with open(f'{D}/csv-{tag}.csv') as f:
        for r in csv.DictReader(f):
            out[(r['dataset'], int(r['line']))] = r
    return out

def scored(r):
    return r['status'] == 'Ok' and r['no_truth'] == 'false' and r['bad_truth'] == 'false'

def summary(rs):
    s = Counter()
    for r in rs.values():
        if scored(r):
            s['scored'] += 1
            s['solved'] += int(r['answer']) <= int(r['truth'])
            s['exact'] += r['exact'] == 'true'
        s['size'] += int(r['answer']) if r['status'] == 'Ok' else 0
        s['cases'] += 1
    return s

for fuel in sys.argv[4:]:
    base_tag = f'{BASE}-{fuel}'
    ba, br = answers(base_tag), rows(base_tag)
    bs = summary(br)
    bpass = sum(p for p, _, _ in ba.values())
    bstop = sum(1 for _, e, _ in ba.values() if e != 'Completed')
    print(f'--- fuel {fuel}: baseline {base_tag}: {bs["cases"]} cases, {bs["scored"]} scored, '
          f'{bs["solved"]} solved, {bs["exact"]} exact, answer nodes {bs["size"]}, '
          f'pass work {bpass}, stopped {bstop}')
    for tag in sys.argv[3].split(','):
        tag = f'{tag}-{fuel}'
        try:
            a, r = answers(tag), rows(tag)
        except FileNotFoundError:
            print(f'{tag}: missing')
            continue
        s = summary(r)
        missing = len(ba) - len(a)
        changed = [k for k in a if k in ba and a[k][2] != ba[k][2]]
        by_ds = Counter()
        bigger = smaller = 0
        for (ds, ln), x in r.items():
            y = br.get((ds, ln))
            if y and x['status'] == 'Ok' and y['status'] == 'Ok' and x['answer'] != y['answer']:
                by_ds[ds] += 1
                bigger += int(x['answer']) > int(y['answer'])
                smaller += int(x['answer']) < int(y['answer'])
        p = sum(v[0] for v in a.values())
        stop = sum(1 for _, e, _ in a.values() if e != 'Completed')
        print(f'{tag:>20}: {len(a)} answers ({missing} missing), {len(changed)} texts changed, '
              f'size changed {sum(by_ds.values())} (+{bigger} / -{smaller}), solved {s["solved"]} '
              f'(base {bs["solved"]}), exact {s["exact"]} (base {bs["exact"]}), '
              f'pass work {p} ({p / max(bpass, 1):.2f}x), stopped {stop}')
        for ds, n in by_ds.most_common(8):
            print(f'{"":>24}{ds}: {n}')
