#!/bin/sh
# Exhaustive g(n) for n = 1..NMAX (default 11): every poset from nauty's genposetg (Hasse diagrams as digraph6),
# e(P) by a DP over down-sets, #Aut(P) by backtracking (orbits.c); compares n, #posets, g(n), #maximisers with
# expected.txt (poset counts = OEIS A000112). n = 11 takes a few minutes.
# Needs nauty's genposetg on PATH (or GENPOSETG=/path/to/genposetg) and a C compiler.
set -e
NMAX=${1:-11}
GEN=${GENPOSETG:-genposetg}
cc -O2 -o orbits orbits.c
: > search_out.txt
for n in $(seq 1 "$NMAX"); do
  "$GEN" "$n" t q 2>/dev/null | ./orbits | python3 maxima.py | tee -a search_out.txt | cut -c1-100
done
if cut -d' ' -f1-4 search_out.txt | diff - "$(head -n "$NMAX" expected.txt > expected_n.txt; echo expected_n.txt)" >/dev/null; then
  echo "ALL PASS"; else echo "FAILED"; exit 1; fi
