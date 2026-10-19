"""Summarizes --solver-calls dumps (bitwright-bench, feature probe) and BW_CALLS dumps of the
compare harness: per corpus, the distribution of instructions, CPU time and steps per solver
call, instructions per step, and the solver's share of the run.

    calls.py FILE [--by-answer] [--group PREFIXLEN]

C lines: C corpus input call nodes vars limit steps answer memo instr ns cpu_ns left cap
T lines: T corpus inputs instr=... pass=... ms=...
"""
import sys
from collections import defaultdict

ANSWERS = ['simplified', 'no simpler', 'unsupported', 'exhausted']


def q(xs, p):
    if not xs:
        return 0
    xs = sorted(xs)
    i = min(len(xs) - 1, max(0, int(round(p * (len(xs) - 1)))))
    return xs[i]


def fmt(x, unit=''):
    if x >= 1e9:
        return f'{x / 1e9:.2f} G{unit}'
    if x >= 1e6:
        return f'{x / 1e6:.2f} M{unit}'
    if x >= 1e3:
        return f'{x / 1e3:.1f} k{unit}'
    return f'{x:.0f}{unit}'


def load(path):
    calls = defaultdict(list)
    totals = {}
    span = (0.0, 0.0)
    with open(path) as f:
        for line in f:
            if line.startswith('#'):
                if 'span' in line:
                    t = line.split('span')[1].split()
                    span = (float(t[0]), float(t[2]))
                continue
            p = line.rstrip('\n').split('\t')
            if p[0] == 'C':
                corpus = p[1]
                nodes, vars_, limit, steps, answer, memo, instr, ns = map(int, p[4:12])
                cpu = int(p[12]) if len(p) > 14 else 0
                calls[corpus].append(dict(nodes=nodes, vars=vars_, limit=limit, steps=steps,
                                          answer=answer, memo=memo, instr=instr, ns=ns,
                                          cpu=cpu, input=p[2]))
            elif p[0] == 'T':
                kv = dict(x.split('=', 1) for x in p[3:] if '=' in x)
                totals[p[1]] = kv
    return calls, totals, span


def main():
    path = sys.argv[1]
    calls, totals, (span_i, span_ns) = load(path)
    print(f'# {path}: span {span_i:.0f} instr subtracted per call')
    hdr = (f'{"corpus":<24}{"calls":>7}{"memo":>6}{"exh":>5}{"solver %":>9}'
           f'{"instr p50":>11}{"p99":>10}{"max":>10}{"cpu p50":>10}{"p99":>9}{"max":>9}'
           f'{"steps p50":>11}{"p99":>9}{"max":>9}{"i/step":>8}{"ns/step":>8}{"i/step p10-p90":>16}')
    print(hdr)
    for corpus, cs in calls.items():
        real = [c for c in cs if not c['memo']]
        instr = [max(0, c['instr'] - span_i) for c in cs]
        cpu = [c['cpu'] for c in cs]
        steps = [c['steps'] for c in cs]
        tot = totals.get(corpus, {})
        run_instr = float(tot.get('instr', 0))
        solver_instr = sum(instr)
        share = 100 * solver_instr / run_instr if run_instr else float('nan')
        si = sum(max(0, c['instr'] - span_i) for c in real)
        ss = sum(c['steps'] for c in real)
        sc = sum(c['cpu'] for c in real)
        ratios = [(c['instr'] - span_i) / c['steps'] for c in real if c['steps'] >= 1000]
        exh = sum(1 for c in cs if c['answer'] == 3)
        print(f'{corpus:<24}{len(cs):>7}{len(cs) - len(real):>6}{exh:>5}{share:>8.1f}%'
              f'{fmt(q(instr, .5)):>11}{fmt(q(instr, .99)):>10}{fmt(max(instr)):>10}'
              f'{fmt(q(cpu, .5) / 1e3, "us") if cpu[0] or max(cpu) else "-":>10}'
              f'{fmt(q(cpu, .99) / 1e3, "us"):>9}{fmt(max(cpu) / 1e3, "us"):>9}'
              f'{fmt(q(steps, .5)):>11}{fmt(q(steps, .99)):>9}{fmt(max(steps)):>9}'
              f'{si / max(ss, 1):>8.0f}{sc / max(ss, 1):>8.1f}'
              f'{q(ratios, .1):>8.0f}-{q(ratios, .9):<7.0f}')
    if '--by-answer' in sys.argv:
        print()
        print(f'{"corpus":<24}{"answer":<12}{"calls":>7}{"instr sum":>12}{"steps sum":>12}{"i/step":>8}{"instr p50":>11}{"max":>10}')
        for corpus, cs in calls.items():
            for a in range(4):
                sel = [c for c in cs if c['answer'] == a and not c['memo']]
                if not sel:
                    continue
                si = sum(c['instr'] - span_i for c in sel)
                ss = sum(c['steps'] for c in sel)
                print(f'{corpus:<24}{ANSWERS[a]:<12}{len(sel):>7}{fmt(si):>12}{fmt(ss):>12}'
                      f'{si / max(ss, 1):>8.0f}{fmt(q([c["instr"] for c in sel], .5)):>11}'
                      f'{fmt(max(c["instr"] for c in sel)):>10}')


main()
