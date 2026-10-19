# Solver-budget investigation (prototype)

Scripts behind `docs/proposals/solver-budget.md`. The switches they set (`BW_SOLVER_MODE`,
`BW_SOLVER_RATE`, `BW_SOLVER_ACCOUNT`, `BW_SOLVER_ROUND`, `BW_SOLVER_FLOOR`, see
`bitwright/src/mba/probe.rs`), the bench modes and `compare/`'s `BW_CALLS` are a prototype, not
meant to land. They combine with the symbolic-charge switches (`tools/symbolic-charge/`).

Every solver call the engine makes, at the default budget (feature `probe`; a separate target
directory keeps the plain build):

```text
CARGO_TARGET_DIR=target/probe cargo build --release -p bitwright-bench --features probe
taskset -c 0-7 target/probe/release/bitwright-bench --solver-calls calls.tsv
python3 tools/solver-budget/table.py calls.tsv          # per-call table rows
python3 tools/solver-budget/calls.py calls.tsv --by-answer
python3 tools/solver-budget/runs.py calls.tsv           # per-run totals, worst calls
python3 tools/solver-budget/demand.py calls.tsv         # what a charge at rate R would demand
```

More random DAGs (`count,nodes,symbols,bits[,heavy]`), with the questions of calls over 0.3 G
instructions dumped; then a hill climb from them, one question at three budgets, and the
questions as expressions through the engine at seven fuels:

```text
BW_DUMP_OVER=300000000 BW_DUMP_FILE=dump.tsv \
    target/probe/release/bitwright-bench --solver-dags 50,200,6,8 dags.tsv
target/probe/release/bitwright-bench --solver-search dump.tsv 200
target/probe/release/bitwright-bench --solver-worst dump.tsv
python3 tools/solver-budget/to_text.py dump.tsv > dump.txt
target/probe/release/bitwright-bench --solver-fuel dump.txt 8
```

Where the time goes (frame pointers, a target directory of its own):

```text
RUSTFLAGS="-C force-frame-pointers=yes -g" CARGO_TARGET_DIR=target/probe-fp \
    cargo build --release -p bitwright-bench --features probe
perf record -e cpu_core/instructions/u -c 1000000 --call-graph fp -o q.data \
    target/probe-fp/release/bitwright-bench --solver-worst q.tsv
perf script -i q.data | python3 tools/solver-budget/fold.py 14
```

`--prover-budgets` and per-root results at seven budgets per configuration line
`mode rate account round`, then compared with today's:

```text
cargo build --release -p bitwright-bench
printf '%s\n' "off 64 256 exact" "bound 4 256 exact" "account 64 4 exact" |
    tools/solver-budget/sweeps.sh target/release/bitwright-bench out
python3 tools/solver-budget/sweep_tables.py out/sweep-off-64-256-exact.tsv \
    "bound 4=out/sweep-bound-4-256-exact.tsv" "account 4=out/sweep-account-64-4-exact.tsv"
```

bw-nf on CoBRA's datasets (see `compare/README.md`), per line `mode rate account round fuel`,
then compared with today's (`tools/symbolic-charge/cmp_compare.py`); with the probe build,
`compare-calls.sh` also records every solver call and each line's instructions
(`cobra_share.py` sums them by dataset):

```text
(cd compare && cargo build --release --bin bitwright-compare)
printf '%s\n' "off 64 256 exact default" "bound 4 256 exact 12" |
    tools/solver-budget/compare-runs.sh compare/target/release/bitwright-compare \
    compare/work/cobra-data/test/datasets cobra
python3 tools/symbolic-charge/cmp_compare.py cobra off-64-256-exact bound-4-256-exact default 12
(cd compare && cargo build --release --bin bitwright-compare --features probe)
printf '%s\n' "0 off 64 256 default" "1 bound 4 256 12" |
    tools/solver-budget/compare-calls.sh compare/target/release/bitwright-compare \
    compare/work/cobra-data/test/datasets cobra-calls
python3 tools/solver-budget/cobra_share.py cobra-calls/calls-s0-off-64-256-default.tsv
```
