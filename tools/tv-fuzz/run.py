#!/usr/bin/env python3
"""Translation validation against LLVM itself.

For each seed: random functions (integer, or floating point with --float), optimized by clang
at -O2, must all validate (`bitwright tv` never says INVALID). Then each optimized module is
mutated three times; every mutant bitwright judges invalid must be confirmed by the independent
interpreter at the counterexample's inputs, and in every mutant it judges valid, random
sampling with the interpreter must find no input where the mutant fails to refine the source
(integer functions only: the interpreter has no floating point).

    tools/tv-fuzz/run.py --bitwright target/release/bitwright --clang clang-21 --seeds 8
"""
import argparse, os, random, re, subprocess, sys, tempfile

HERE = os.path.dirname(os.path.abspath(__file__))
sys.path.insert(0, HERE)
import interp  # noqa: E402


def sh(args, **kw):
    return subprocess.run(args, capture_output=True, text=True, **kw)


def reports(text):
    """(verdict, function, block of text) per function of a `bitwright tv` report."""
    for b in re.split(r'(?m)^(?=valid |INVALID |unknown |unsupported )', text):
        m = re.match(r'(valid|INVALID|unknown|unsupported)\s+(\S+)', b)
        if m:
            yield m.group(1), m.group(2), b


def sample_args(f, rnd):
    args = []
    for (_, w, noundef) in f["params"]:
        r = rnd.random()
        if r < 0.1 and not noundef:
            args.append(interp.POISON)
        elif r < 0.5:
            args.append(rnd.choice([0, 1, (1 << w) - 1, 1 << (w - 1), (1 << (w - 1)) - 1, 2, 3, 7, 8]) & ((1 << w) - 1))
        else:
            args.append(rnd.randrange(1 << w))
    return args


def main():
    ap = argparse.ArgumentParser()
    ap.add_argument("--bitwright", default="target/release/bitwright")
    ap.add_argument("--clang", default="clang")
    ap.add_argument("--seeds", type=int, default=8)
    ap.add_argument("--functions", type=int, default=100)
    ap.add_argument("--float", action="store_true")
    ap.add_argument("--samples", type=int, default=1500)
    a = ap.parse_args()
    gen = os.path.join(HERE, "gen_float.py" if a.float else "gen_int.py")
    stats = dict(original_valid=0, original_invalid=0, undecided=0, mutants_valid=0,
                 mutants_invalid=0, unconfirmed=0, unsound=0)
    with tempfile.TemporaryDirectory() as d:
        for seed in range(1, a.seeds + 1):
            src, out, mut = (os.path.join(d, n) for n in ("in.ll", "out.ll", "mut.ll"))
            with open(src, "w") as fh:
                fh.write(sh(["python3", gen, str(seed), str(a.functions)]).stdout)
            r = sh([a.clang, "-x", "ir", "-O2", "-S", "-emit-llvm", src, "-o", out])
            if r.returncode:
                sys.exit(r.stderr)
            for verdict, name, block in reports(sh([a.bitwright, "tv", src, out]).stdout):
                if verdict == "valid":
                    stats["original_valid"] += 1
                elif verdict == "INVALID":
                    stats["original_invalid"] += 1
                    print(f"seed {seed}: the optimizer's {name} is INVALID\n{block}")
                else:
                    stats["undecided"] += 1
            if a.float:
                continue
            fsrc = interp.parse(open(src).read())
            for m in range(3):
                sh(["python3", os.path.join(HERE, "mutate.py"), str(100 * seed + m), out, mut,
                    os.path.join(d, "mut.log")])
                ftgt = interp.parse(open(mut).read())
                rnd = random.Random(seed * 7 + m)
                for verdict, name, block in reports(sh([a.bitwright, "tv", src, mut]).stdout):
                    f, g = fsrc.get(name), ftgt.get(name)
                    if f is None or g is None:
                        continue
                    if verdict == "valid":
                        stats["mutants_valid"] += 1
                        for _ in range(a.samples):
                            args = sample_args(f, rnd)
                            s, t = interp.behaviors(f, args, rnd), interp.behaviors(g, args, rnd)
                            if not interp.refines(s, t):
                                stats["unsound"] += 1
                                print(f"seed {seed}/{m} {name}: judged valid, but {args}: {s} then {t}")
                                break
                    elif verdict == "INVALID":
                        stats["mutants_invalid"] += 1
                        args = []
                        for (p, w, _) in f["params"]:
                            v = re.search(r'^\s+' + re.escape(p) + r' = i\d+ (\S+)', block, re.M).group(1)
                            args.append(interp.POISON if v == "poison" else
                                        int(v == "true") if v in ("true", "false") else int(v) & ((1 << w) - 1))
                        # The target's freeze choices are random: a few tries.
                        if not any(not interp.refines(interp.behaviors(f, args, rnd), interp.behaviors(g, args, rnd))
                                   for _ in range(30)):
                            stats["unconfirmed"] += 1
                            print(f"seed {seed}/{m} {name}: counterexample not confirmed\n{block}")
    print(stats)
    bad = stats["original_invalid"] + stats["unconfirmed"] + stats["unsound"]
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
