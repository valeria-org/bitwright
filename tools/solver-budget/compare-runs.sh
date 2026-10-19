#!/bin/bash
# PROTOTYPE (solver-budget investigation): one bw-nf run of the compare harness over CoBRA's
# datasets per configuration line "mode rate account round fuel" on stdin (mode off, charge,
# bound, derive, scale or account; round exact or pow2; fuel "default" for the default budget,
# else N for Budget::fuel(2^N)), JOBS at a time. Writes ans-TAG.tsv, csv-TAG.csv and
# log-TAG.txt to OUT, TAG = mode-rate-account-round-fuel.
#   tools/solver-budget/compare-runs.sh BIN DATASETS OUT < configs.txt
set -u
BIN=$1 DS=$2 OUT=$3
mkdir -p "$OUT"
run() {
  mode=$1; rate=$2; account=$3; round=$4; fuel=$5
  tag=$mode-$rate-$account-$round-$fuel
  rm -f "$OUT/ans-$tag.tsv"
  if [ "$fuel" = default ]; then unset BW_FUEL; else export BW_FUEL=$fuel; fi
  BW_SOLVER_MODE=$mode BW_SOLVER_RATE=$rate BW_SOLVER_ACCOUNT=$account BW_SOLVER_ROUND=$round \
    BW_ANSWERS="$OUT/ans-$tag.tsv" nice -n 5 "$BIN" "$DS" --skip oses_all --tools bw-nf \
    --csv "$OUT/csv-$tag.csv" > "$OUT/log-$tag.txt" 2>&1
  echo "done $tag"
}
export -f run
export BIN DS OUT
xargs -P "${JOBS:-4}" -L 1 bash -c 'run $0 $1 $2 $3 $4'
