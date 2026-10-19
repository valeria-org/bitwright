"""Line-by-line comparison of BW_ANSWERS dumps of the compare harness (every run writes the
cases in the same order).

    cmp_answers.py DIR BASE TAG1,TAG2,... FUEL...

Compares DIR/ans-TAG-FUEL.tsv with DIR/ans-BASE-FUEL.tsv: answers changed and pass work."""
import sys

D, BASE = sys.argv[1], sys.argv[2]


def load(tag):
    with open(f'{D}/ans-{tag}.tsv') as f:
        return [l.rstrip('\n').split('\t', 4) for l in f]


for fuel in sys.argv[4:]:
    base = load(f'{BASE}-{fuel}')
    bp = sum(int(x[2]) for x in base)
    print(f'fuel {fuel}: {len(base)} cases, pass work {bp}')
    for tag in sys.argv[3].split(','):
        a = load(f'{tag}-{fuel}')
        assert len(a) == len(base) and all(x[0] == y[0] and x[1] == y[1] for x, y in zip(a, base))
        changed = sum(1 for x, y in zip(a, base) if x[4] != y[4])
        p = sum(int(x[2]) for x in a)
        print(f'  {tag:>16}: {changed} answers changed, pass work {p} ({p / bp:.2f}x)')
