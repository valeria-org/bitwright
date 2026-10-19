"""Writes questions of --solver-worst files (the last tab-separated field of each line) as
expressions in bitwright's syntax, one per line, variables x0, x1, ... (a tree: shared nodes
are repeated; the parser shares them again). Widths come from ParseOptions."""
import sys

for line in open(sys.argv[1]):
    q = line.rstrip('\n').split('\t')[-1]
    vars_, nodes = q.split(';', 1)
    out = []
    for tok in nodes.split():
        op, _, args = tok.partition('@')
        a = [out[int(x)] for x in args.split(',')] if args else []
        if op.startswith('v'):
            t = f'x{op[1:]}'
        elif op.startswith('c'):
            hexv, w = op[1:].split(':')
            t = f'0x{hexv}'
        elif op.startswith('<<'):
            t = f'({a[0]} << {op[2:]})'
        elif op.startswith('>>'):
            t = f'({a[0]} >>u {op[2:]})'
        elif ':' in op:
            c, w = op.split(':')
            f = {'zx': 'zext', 'sx': 'sext', 'tr': 'trunc'}[c]
            t = f'{f}<{w}>({a[0]})'
        elif op == 'n':
            t = f'(-{a[0]})'
        elif op == '~':
            t = f'(~{a[0]})'
        else:
            t = f'({a[0]} {op} {a[1]})'
        out.append(t)
    print(out[-1])
