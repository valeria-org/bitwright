"""Markdown rows for the per-call table: per corpus (or group of corpora), solver calls (memo
hits), instructions, CPU time and steps per call (median, p99, max), instructions and CPU
nanoseconds per step over calls that solved (not from the memo), and the solver's share of the
run's instructions (from T or R lines).

    table.py FILE [GROUP=PREFIX,PREFIX...]...
"""
import sys
from collections import defaultdict


def q(xs, p):
    xs = sorted(xs)
    return xs[min(len(xs) - 1, max(0, int(round(p * (len(xs) - 1)))))] if xs else 0


def fmt(x):
    if x >= 1e9:
        return f'{x / 1e9:.2f} G'
    if x >= 1e6:
        return f'{x / 1e6:.1f} M'
    if x >= 1e3:
        return f'{x / 1e3:.0f} k'
    return f'{x:.0f}'


def ms(ns):
    if ns >= 1e9:
        return f'{ns / 1e9:.2f} s'
    if ns >= 1e6:
        return f'{ns / 1e6:.1f} ms'
    return f'{ns / 1e3:.0f} µs'


path = sys.argv[1]
groups = []
for g in sys.argv[2:]:
    name, prefixes = g.split('=', 1)
    groups.append((name, prefixes.split(',')))
span = 0.0
calls = defaultdict(list)
run_instr = defaultdict(float)
run_from_r = defaultdict(float)
for line in open(path):
    if line.startswith('#') and 'span' in line:
        span = float(line.split('span')[1].split()[0])
        continue
    p = line.rstrip('\n').split('\t')
    if p[0] == 'C':
        calls[p[1]].append((max(0, int(p[10]) - span), int(p[12]), int(p[7]), p[9] == '1'))
    elif p[0] == 'T':
        kv = dict(x.split('=', 1) for x in p[3:] if '=' in x)
        run_instr[p[1]] += float(kv['instr'])
    elif p[0] == 'R':
        kv = dict(x.split('=', 1) for x in p[3:] if '=' in x)
        run_from_r[p[1]] += float(kv['instr'])
for k, v in run_from_r.items():
    run_instr.setdefault(k, v)
if not groups:
    groups = [(c, [c]) for c in calls]
for name, prefixes in groups:
    sel = [c for k, cs in calls.items() if any(k.startswith(x) for x in prefixes) for c in cs]
    ri = sum(v for k, v in run_instr.items() if any(k.startswith(x) for x in prefixes))
    if not sel:
        continue
    instr = [c[0] for c in sel]
    cpu = [c[1] for c in sel]
    steps = [c[2] for c in sel]
    real = [c for c in sel if not c[3] and c[2] > 0]
    si, ss, sc = sum(c[0] for c in real), sum(c[2] for c in real), sum(c[1] for c in real)
    ratios = [c[0] / c[2] for c in real if c[2] >= 1000]
    share = f'{100 * sum(instr) / ri:.0f} %' if ri else '-'
    print(f'| {name} | {len(sel):,} ({sum(1 for c in sel if c[3]):,}) | {fmt(q(instr, .5))} / {fmt(q(instr, .99))} / {fmt(max(instr))} '
          f'| {ms(q(cpu, .5))} / {ms(q(cpu, .99))} / {ms(max(cpu))} '
          f'| {fmt(q(steps, .5))} / {fmt(q(steps, .99))} / {fmt(max(steps))} '
          f'| {si / max(ss, 1):.0f} ({q(ratios, .01):.0f} to {max(ratios) if ratios else 0:,.0f}) | {sc / max(ss, 1):.0f} | {share} |')
