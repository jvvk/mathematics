#!/bin/sh
# Enumerate every squared rectangle with at most K squares and report every tiling of 697 x 611.
# Usage: sh run.sh [K]   (default K = 14; K = 13 proves the lower bound, K = 14 finds the tiling)
# Needs a C compiler. plantri 5.8 (Brinkmann and McKay, Apache 2.0) is built from tools/plantri58.tar.gz.
set -e
K=${1:-14}
cd "$(dirname "$0")"
mkdir -p build out
[ -x build/plantri58/plantri ] || { tar -xzf tools/plantri58.tar.gz -C build && make -C build/plantri58 plantri >/dev/null; }
cc -O2 -o build/sqrect sqrect.c -lm
nv=4
while [ $nv -le $((K + 3)) ]; do
  # a tiling with k squares is a 2-connected plane multigraph with k + 1 edges:
  # one colour class of the quadrangulations with k + 1 faces, which have k + 3 vertices
  build/plantri58/plantri -qc2m2 $nv 2>/dev/null | build/sqrect out/best_$nv.txt > out/hits_$nv.txt
  echo "nv=$nv ($((nv - 3)) squares): $(grep -c 'HIT' out/hits_$nv.txt || true) tilings of 697x611 or 1394x1222"
  nv=$((nv + 1))
done
