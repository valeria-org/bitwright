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

clang must be recent enough to print the flags the generator's instructions get (`or
disjoint`, `samesign`: LLVM 20 or later).
