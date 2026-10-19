# Symbolic-charge investigation (prototype)

Scripts behind `docs/proposals/symbolic-charge.md`. The switches they set
(`BW_SYMBOLIC_CHARGE`, `BW_SYMBOLIC_MODE`, `BW_SYMBOLIC_RESERVE`, `BW_SYMBOLIC_SCOPE`, see
`bitwright/src/mba/probe.rs`) and the bench and compare modes they read are a prototype, not
meant to land.

Per-root results on the bench and `--corpus-diff` corpora at seven budgets, one file per
setting, then compared with today's:

```text
cargo build --release -p bitwright-bench
target/release/bitwright-bench --symbolic-sweep sweep-1.tsv
BW_SYMBOLIC_CHARGE=256 BW_SYMBOLIC_MODE=bound BW_SYMBOLIC_RESERVE=0 \
    target/release/bitwright-bench --symbolic-sweep sweep-256.tsv
python3 tools/symbolic-charge/cmp_sweep.py sweep-1.tsv sweep-256.tsv
```

bw-nf on CoBRA's datasets (see `compare/README.md` for the datasets), one run per line of
`mode k fuel reserve`:

```text
(cd compare && cargo build --release --bin bitwright-compare)
printf '%s\n' "clamp 1 default 1" "clamp 1 10 1" "bound 256 default 0" "bound 256 10 0" |
    tools/symbolic-charge/compare-runs.sh compare/target/release/bitwright-compare \
    compare/work/cobra-data/test/datasets target/symcharge
python3 tools/symbolic-charge/cmp_answers.py target/symcharge clamp-1-r1 bound-256-r0 default 10
python3 tools/symbolic-charge/cmp_compare.py target/symcharge clamp-1-r1 bound-256-r0 default 10
```

Instructions and time per charged unit by kind of work, and the longest single comparison
(feature `probe`; a separate target directory keeps the plain build):

```text
CARGO_TARGET_DIR=target/probe cargo build --release -p bitwright-bench --features probe
taskset -c 5 target/probe/release/bitwright-bench --symbolic-cost
target/probe/release/bitwright-bench --symbolic-worst
```
