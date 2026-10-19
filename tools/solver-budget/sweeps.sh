#!/bin/bash
# PROTOTYPE (solver-budget investigation): --symbolic-sweep and --prover-budgets per
# configuration line "mode rate account round" on stdin, JOBS at a time, into OUT
# (sweep-TAG.tsv, pb-TAG.txt; TAG = mode-rate-account-round).
#   tools/solver-budget/sweeps.sh BIN OUT < configs.txt
set -u
BIN=$1 OUT=$2
mkdir -p "$OUT"
run() {
  mode=$1; rate=$2; account=$3; round=$4
  tag=$mode-$rate-$account-$round
  export BW_SOLVER_MODE=$mode BW_SOLVER_RATE=$rate BW_SOLVER_ACCOUNT=$account BW_SOLVER_ROUND=$round
  nice -n 5 "$BIN" --prover-budgets > "$OUT/pb-$tag.txt" 2>&1
  nice -n 5 "$BIN" --symbolic-sweep "$OUT/sweep-$tag.tsv" > "$OUT/sweep-$tag.log" 2>&1
  echo "done $tag"
}
export -f run
export BIN OUT
xargs -P "${JOBS:-4}" -L 1 bash -c 'run $0 $1 $2 $3'
