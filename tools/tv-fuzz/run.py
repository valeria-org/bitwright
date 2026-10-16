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
    return interp.random_args(f, rnd)


def target_choices(block):
    """The values the counterexample's target computed, by register (its freezes' choices
    among them)."""
    target = block.split("\ntarget:\n", 1)
    if len(target) < 2:
        return {}
    out = {}
    for m in re.finditer(r'(?m)^  (%[\w.]+) = i\d+ (\S+)$', target[1]):
        v = m.group(2)
        if v not in ("poison",):
            out[m.group(1)] = int(v == "true") if v in ("true", "false") else int(v)
    return out


def confirmed(f, g, args, block, rnd, tries=300):
    """Whether the counterexample holds in the interpreter: the target's execution with the
    report's choices is matched by no execution of the source found (the source's one
    execution, when it makes no choices)."""
    t = interp.behaviors(g, args, rnd, chosen=target_choices(block))
    trace = {}
    s = interp.behaviors(f, args, rnd, trace=trace)
    if interp.refines(s, t):
        return False
    if not trace.get("freeze"):
        return True
    return not any(interp.refines(interp.behaviors(f, args, rnd), t) for _ in range(tries))


def refinement_sample(f, g, args, rnd, tries=300):
    """Whether the target `g` refines the source `f` at `args`, by sampling: None when it
    does, "inconclusive" when a nondeterministic source might match with choices not found,
    else the failing behaviors. Freezing a poison parameter gives one value in both programs
    (a choice each may make); a mismatch then searches the source's other choices."""
    frozen = [rnd.randrange(1 << p["w"]) for p in f["params"]]
    by_name = lambda h: {p["name"]: v for p, v in zip(h["params"], frozen)}
    trace = {}
    t = interp.behaviors(g, args, rnd, by_name(g))
    s = interp.behaviors(f, args, rnd, by_name(f), trace)
    if interp.refines(s, t):
        return None
    if not trace.get("freeze"):
        return f"{s} then {t}"
    if any(interp.refines(interp.behaviors(f, args, rnd), t) for _ in range(tries)):
        return None
    return "inconclusive"


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
                 mutants_invalid=0, mutants_undecided=0, unconfirmed=0, unsound=0,
                 inconclusive=0)
    with tempfile.TemporaryDirectory() as d:
        for seed in range(1, a.seeds + 1):
            src, out, mut = (os.path.join(d, n) for n in ("in.ll", "out.ll", "mut.ll"))
            with open(src, "w") as fh:
                fh.write(sh([sys.executable, gen, str(seed), str(a.functions)]).stdout)
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
                sh([sys.executable, os.path.join(HERE, "mutate.py"), str(100 * seed + m), out, mut,
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
                            verdict = refinement_sample(f, g, args, rnd)
                            if verdict == "inconclusive":
                                stats["inconclusive"] += 1
                            elif verdict is not None:
                                stats["unsound"] += 1
                                print(f"seed {seed}/{m} {name}: judged valid, but {args}: {verdict}")
                                break
                    elif verdict == "INVALID":
                        stats["mutants_invalid"] += 1
                        args = []
                        for prm in f["params"]:
                            p, w = prm["name"], prm["w"]
                            v = re.search(r'^\s+' + re.escape(p) + r' = i\d+ (\S+)', block, re.M).group(1)
                            args.append(interp.POISON if v == "poison" else
                                        int(v == "true") if v in ("true", "false") else int(v) & ((1 << w) - 1))
                        if not confirmed(f, g, args, block, rnd):
                            stats["unconfirmed"] += 1
                            print(f"seed {seed}/{m} {name}: counterexample not confirmed\n{block}")
                    else:
                        stats["mutants_undecided"] += 1
    print(stats)
    bad = stats["original_invalid"] + stats["unconfirmed"] + stats["unsound"]
    sys.exit(1 if bad else 0)


if __name__ == "__main__":
    main()
