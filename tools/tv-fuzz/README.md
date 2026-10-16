# Translation validation against LLVM

`run.py` checks `bitwright tv` against LLVM's own optimizer and an independent interpreter:
random functions (`gen_int.py`, or `gen_float.py` with `--float`) are optimized by clang at
`-O2`, and every result must validate; each optimized module is then mutated (`mutate.py`), and
the mutants bitwright calls invalid must fail at the counterexample in `interp.py` (a small
interpreter of the integer subset with LLVM's poison and undefined behavior), while random
sampling must find no failure in the ones it calls valid.

```sh
cargo build --release -p bitwright-cli
python3 tools/tv-fuzz/run.py --bitwright target/release/bitwright --clang clang-21 --seeds 8
python3 tools/tv-fuzz/run.py --bitwright target/release/bitwright --clang clang-21 --float
```

(On Windows, give `--bitwright` as an absolute path.) clang must be recent enough to print the
flags the generator's instructions get (`or disjoint`, `samesign`: LLVM 20 or later).

What it covers:

- **Functions:** straight-line code and diamonds joined by a phi, over the integer
  instructions with their poison flags, `select`, `freeze`, `ctpop` (clang writes a `range`
  on its result) and the min/max intrinsics, at 8, 16 and 32 bits.
- **Mutants:** a constant moved by one; an operation or a predicate changed; a poison flag
  dropped or *added* (`nuw`, `nsw`, `exact`, `disjoint`, `samesign`, `nneg`); a `noundef` or a
  `range` added to a parameter, a `range` to the return value, a `noundef` to a call's
  argument or result; the entries of a phi swapped. Each function reads its parameters
  through its own attributes, in bitwright and in the interpreter alike.
- **Nondeterminism:** freezing a poison value has many results. A counterexample is replayed
  with the target's choices from the report, against the source's (its one execution when it
  makes none, else many). For a mutant judged valid, freezing a poison parameter gives one
  value in both programs, and a mismatch searches the source's other choices; a sample that
  search cannot settle is counted `inconclusive`, never `unsound`.

The run fails on an optimized function judged invalid, a counterexample the interpreter does
not confirm, or a sampled failure of a mutant judged valid.
