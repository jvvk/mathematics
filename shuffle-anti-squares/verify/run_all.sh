#!/usr/bin/env bash
# Every computer check behind the paper, from a fresh clone; stops at the first failure.
# Needs a C and a C++17 compiler, python3 and z3-solver. About 45 minutes on one core (length 34 dominates).
set -euo pipefail
cd "$(dirname "$0")"
LENGTHS="2 4 6 8 10 12 14 16 18 20 22 24 26 28 30 32 34"

echo "== search: antisq at every even length up to 34"
cd search
cc -O2 -o antisq antisq.c
for n in $LENGTHS; do
  ./antisq "$n" > "anti_$n.txt"
  if [ "$n" -lt 24 ]; then
    [ ! -s "anti_$n.txt" ] || { echo "FAIL: anti-square found at length $n"; exit 1; }
  else
    cmp -s <(sort "anti_$n.txt") <(sort "../results/anti_$n.txt") || { echo "FAIL: length $n differs from results/"; exit 1; }
  fi
done
python3 classes.py ../results/anti_*.txt
python3 ilp_proof.py prove
python3 ilp_proof.py validate 200
python3 validate_neg.py
python3 mutation.py

echo "== cutting: two cuts suffice for every rotation of every anti-square up to length 34"
cd ../cutting
cc -O2 -o cutdist cutdist.c
for n in 24 26 28 30 32 34; do ./cutdist < "../results/anti_$n.txt" > /dev/null; done
python3 cutdist_check.py

echo "== recheck: independent enumerator and two-cut test, every even length up to 34"
cd ../recheck
c++ -O2 -std=c++17 -o indep indep.cpp
for n in $LENGTHS; do ./indep "$n" > "anti_$n.txt"; done
python3 compare.py ../results
python3 remark5.py

echo "ALL CHECKS PASSED"
