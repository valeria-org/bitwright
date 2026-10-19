#!/bin/bash
# PROTOTYPE (solver-budget investigation): like compare-runs.sh, with the probe build of the
# compare harness: BW_CALLS records every solver call and each line's engine instructions.
# Configuration lines "sym mode rate account fuel" (sym: 1 for the symbolic-charge
# recommendation, k = 256, bound, no reserve; else 0).
#   tools/solver-budget/compare-calls.sh PROBE_BIN DATASETS OUT < configs.txt
set -u
BIN=$1 DS=$2 OUT=$3
mkdir -p "$OUT"
run() {
  sym=$1; mode=$2; rate=$3; account=$4; fuel=$5
  tag=s$sym-$mode-$rate-$account-$fuel
  rm -f "$OUT/calls-$tag.tsv" "$OUT/ans-$tag.tsv"
  if [ "$fuel" = default ]; then unset BW_FUEL; else export BW_FUEL=$fuel; fi
  if [ "$sym" = 1 ]; then
    export BW_SYMBOLIC_MODE=bound BW_SYMBOLIC_CHARGE=256 BW_SYMBOLIC_RESERVE=0
  fi
  BW_SOLVER_MODE=$mode BW_SOLVER_RATE=$rate BW_SOLVER_ACCOUNT=$account \
    BW_CALLS="$OUT/calls-$tag.tsv" BW_ANSWERS="$OUT/ans-$tag.tsv" nice -n 5 "$BIN" "$DS" \
    --skip oses_all --tools bw-nf --csv "$OUT/csv-$tag.csv" > "$OUT/log-$tag.txt" 2>&1
  echo "done $tag"
}
export -f run
export BIN DS OUT
xargs -P "${JOBS:-4}" -L 1 bash -c 'run $0 $1 $2 $3 $4'
