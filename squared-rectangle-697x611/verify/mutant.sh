#!/usr/bin/env bash
# Mutation test: an enumeration that drops every network with parallel edges must disagree with OEIS A219158.
set -euo pipefail
cd "$(dirname "$0")"
[ -x build/plantri58/plantri ] || { mkdir -p build && tar -xzf tools/plantri58.tar.gz -C build && make -C build/plantri58 plantri >/dev/null; }
mkdir -p build out_mutant
cc -O2 -DMUTANT -o build/sqrect_mutant sqrect.c -lm
: > out_mutant/summary.txt
for nv in 4 5 6 7 8 9 10 11 12 13 14 15; do
  build/plantri58/plantri -qc2m2 $nv 2> out_mutant/plantri_$nv.err | build/sqrect_mutant out_mutant/best_$nv.txt > /dev/null 2> out_mutant/sqrect_$nv.err
  made=$(sed -n 's/^\([0-9]*\) quadrangulations written.*/\1/p' out_mutant/plantri_$nv.err)
  read_=$(sed -n 's/^graphs=\([0-9]*\) .*/\1/p' out_mutant/sqrect_$nv.err)
  [ -n "$made" ] && [ "$made" = "$read_" ] || { echo "FAIL nv=$nv: plantri wrote '$made', mutant read '$read_'"; exit 1; }
  echo "nv=$nv $(cat out_mutant/sqrect_$nv.err)" >> out_mutant/summary.txt
done
# the mutant must complete (above) and must disagree with the table: check_a219158.py exits 1 on any mismatch
set +e; python3 check_a219158.py 12 out_mutant; rc=$?; set -e
if [ "$rc" -eq 1 ]; then echo "mutant killed (disagrees with A219158)"; else echo "MUTANT NOT KILLED (check exit $rc)"; exit 1; fi
