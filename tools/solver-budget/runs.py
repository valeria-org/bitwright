"""Per-run (per input) totals of a --solver-calls dump: solver steps and instructions per run,
and the worst calls.

    runs.py FILE [CORPUS...]
"""
import sys
from collections import defaultdict

def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, max(0, int(round(p * (len(xs) - 1)))))] if xs else 0

path = sys.argv[1]
want = sys.argv[2:]
runs = defaultdict(lambda: defaultdict(lambda: [0, 0, 0, 0]))
calls = defaultdict(list)
for line in open(path):
    p = line.rstrip('\n').split('\t')
    if p[0] != 'C' or (want and p[1] not in want):
        continue
    corpus, inp = p[1], p[2]
    nodes, vars_, limit, steps, answer, memo, instr, ns = map(int, p[4:12])
    cpu = int(p[12])
    r = runs[corpus][inp]
    r[0] += steps; r[1] += instr; r[2] += 1; r[3] += cpu
    calls[corpus].append((instr, steps, answer, memo, nodes, vars_, cpu, inp, int(p[3])))
for corpus, rs in runs.items():
    st = [r[0] for r in rs.values()]
    ins = [r[1] for r in rs.values()]
    cpu = [r[3] for r in rs.values()]
    n = [r[2] for r in rs.values()]
    print(f'{corpus}: {len(rs)} runs; calls/run p50 {q(n,.5)} max {max(n)}; '
          f'steps/run p50 {q(st,.5)} p90 {q(st,.9)} p99 {q(st,.99)} max {max(st)}; '
          f'instr/run p50 {q(ins,.5)/1e6:.1f} M p99 {q(ins,.99)/1e6:.1f} M max {max(ins)/1e6:.1f} M; '
          f'cpu/run p50 {q(cpu,.5)/1e6:.1f} ms max {max(cpu)/1e6:.1f} ms')
    cs = sorted(calls[corpus], reverse=True)
    print('  worst calls (instr, steps, answer, memo, nodes, vars, cpu ms, input, call, instr/step):')
    for c in cs[:8]:
        print(f'   {c[0]/1e6:9.1f} M {c[1]:>9} {c[2]} {c[3]} {c[4]:>5} {c[5]} {c[6]/1e6:7.1f} ms in {c[7]}.{c[8]} {c[0]/max(c[1],1):8.0f}')
    big = [c for c in cs if c[1] >= 1000 and c[2] != 3]
    r = sorted(c[0] / c[1] for c in big)
    if r:
        print(f'  instr/step over {len(big)} calls of >= 1000 steps (not exhausted): p1 {q(r,.01):.0f} p10 {q(r,.1):.0f} p50 {q(r,.5):.0f} p90 {q(r,.9):.0f} p99 {q(r,.99):.0f} max {max(r):.0f}')
