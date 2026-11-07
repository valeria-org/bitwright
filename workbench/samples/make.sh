#!/bin/sh
# Regenerates corpus.bwt, the trace the Workbench opens with: build the command line first
# (cargo build -p bitwright-cli), or point BITWRIGHT at a binary.
set -e
cd "$(dirname "$0")"
B=${BITWRIGHT:-../../target/debug/bitwright}
$B simplify --width 32 --file corpus-32.txt --trace part-32.bwt > /dev/null
$B simplify --width 64 --file corpus-64.txt --trace part-64.bwt > /dev/null
$B simplify --width 64 --assume 'rsp & 15 == 0' --assume 'idx <u n' \
  --trace part-assume.bwt -- '((rsp + 32) & 15) + zext<64>(idx <=u n)' > /dev/null
# The first expression again under the standard strategy, to compare with.
$B simplify --width 32 --standard --trace part-standard.bwt \
  -- '(((x ^ y) + 2*(x & y)) * 3 + ((x | y) - (x & y))) ^ (~z & z)' > /dev/null
cat part-32.bwt part-64.bwt part-assume.bwt part-standard.bwt > corpus.bwt
rm part-32.bwt part-64.bwt part-assume.bwt part-standard.bwt
