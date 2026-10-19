#!/bin/bash
# PROTOTYPE (symbolic-charge investigation): one bw-nf run of the compare harness over CoBRA's
# datasets per configuration line "mode k fuel reserve" on stdin ("default" for the default
# budget, else N for Budget::fuel(2^N)), JOBS at a time. Writes ans-TAG.tsv, csv-TAG.csv and
# log-TAG.txt to OUT, TAG = mode-k-rRESERVE-fuel.
#   tools/symbolic-charge/compare-runs.sh BIN DATASETS OUT < configs.txt
set -u
BIN=$1 DS=$2 OUT=$3
mkdir -p "$OUT"
run() {
  mode=$1; k=$2; fuel=$3; reserve=$4
  tag=$mode-$k-r$reserve-$fuel
  rm -f "$OUT/ans-$tag.tsv"
  if [ "$fuel" = default ]; then unset BW_FUEL; else export BW_FUEL=$fuel; fi
  BW_SYMBOLIC_CHARGE=$k BW_SYMBOLIC_MODE=$mode BW_SYMBOLIC_RESERVE=$reserve \
    BW_ANSWERS="$OUT/ans-$tag.tsv" nice -n 5 "$BIN" "$DS" --skip oses_all --tools bw-nf \
    --csv "$OUT/csv-$tag.csv" > "$OUT/log-$tag.txt" 2>&1
  echo "done $tag"
}
export -f run
export BIN DS OUT
xargs -P "${JOBS:-6}" -L 1 bash -c 'run $0 $1 $2 $3'
