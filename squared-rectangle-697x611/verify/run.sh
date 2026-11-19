#!/usr/bin/env bash
# Enumerate every squared rectangle with at most K squares; report every tiling of a rectangle similar to 697 x 611.
# Usage: bash run.sh [K]   (default K = 14; K = 13 proves the lower bound, K = 14 finds the tiling)
# Needs a C compiler. plantri 5.8 (Brinkmann and McKay, Apache 2.0) is built from tools/plantri58.tar.gz.
# Fails (nonzero exit) if plantri or sqrect fails, if their graph counts differ, if any exact check fails or any
# case is unresolved, or if a rectangle similar to 697 x 611 is tiled by 13 or fewer squares.
set -euo pipefail
K=${1:-14}
cd "$(dirname "$0")"
mkdir -p build out
[ -x build/plantri58/plantri ] || { tar -xzf tools/plantri58.tar.gz -C build && make -C build/plantri58 plantri >/dev/null; }
cc -O2 -o build/sqrect sqrect.c -lm
: > out/summary.txt
nv=4
while [ "$nv" -le $((K + 3)) ]; do
  # a tiling with k squares is a 2-connected plane multigraph with k + 1 edges:
  # one colour class of the quadrangulations with k + 1 faces, which have k + 3 vertices
  build/plantri58/plantri -qc2m2 "$nv" 2> "out/plantri_$nv.err" | build/sqrect "out/best_$nv.txt" > "out/hits_$nv.txt" 2> "out/sqrect_$nv.err"
  made=$(sed -n 's/^\([0-9]*\) quadrangulations written.*/\1/p' "out/plantri_$nv.err")
  read_=$(sed -n 's/^graphs=\([0-9]*\) .*/\1/p' "out/sqrect_$nv.err")
  [ -n "$made" ] && [ "$made" = "$read_" ] || { echo "FAIL nv=$nv: plantri wrote '$made', sqrect read '$read_'"; exit 1; }
  echo "nv=$nv ($((nv - 3)) squares): $(cat "out/sqrect_$nv.err")" | tee -a out/summary.txt
  nv=$((nv + 1))
done
low=0
for f in out/hits_*.txt; do low=$((low + $(grep -c '^HIT k=\([1-9]\|1[0-3]\) ' "$f" || true))); done
[ "$low" -eq 0 ] || { echo "FAIL: $low tilings similar to 697 x 611 with at most 13 squares"; exit 1; }
upto=$(( K < 13 ? K : 13 ))
if [ "$K" -ge 13 ]; then
  echo "PASS: no rectangle similar to 697 x 611 is tiled by 13 or fewer squares (K = $K)" | tee -a out/summary.txt
else
  echo "no rectangle similar to 697 x 611 is tiled by $upto or fewer squares (K = $K < 13: the lower bound needs K >= 13)" | tee -a out/summary.txt
fi
