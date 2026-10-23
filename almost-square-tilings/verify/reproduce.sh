#!/bin/sh
# Re-run the checks behind the theorem: checksums, the certificate audit, Figure 1, the C search for n <= 19,
# and (with the z3-solver Python package) the second search for n <= 18; add 19 to its list to run that case
# too (a few minutes). Exits nonzero on the first failure.
set -e
cd "$(dirname "$0")"
echo "== checksums of out/"
shasum -a 256 -c SHA256SUMS --quiet
echo "== certificate audit (all remaining cases, all inflations, coverage of 20..20000)"
python3 verify/audit.py .
echo "== Figure 1: Moron's rectangle with moved cut lines tiles R_32"
python3 verify/check.py out/illustr/moron_n32.txt 33 32
echo "== exhaustive search for n <= 19 (skyline search in C)"
cc -O2 -o frame src/frame.c
for n in $(seq 1 19); do printf "n=%s " "$n"; ./frame $((n+1)) $n 1 $((n-1)) 0 1 | tail -1; done
if python3 -c "import z3" 2>/dev/null; then
  echo "== independent exact-cover check for n <= 18 (n = 19 takes a few minutes: add 19 to run it)"
  python3 verify/small_sat.py $(seq 1 18)
fi
