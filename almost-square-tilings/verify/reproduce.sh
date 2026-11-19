#!/usr/bin/env bash
# Re-run the checks behind the theorem: checksums, the certificate audit, Figure 1, the C search for n <= 19,
# and (with the z3-solver Python package) the second search for n <= 18; add 19 to its list to run that case
# too (a few minutes). Every result is compared with Theorem 1; exits nonzero on the first failure or mismatch.
set -euo pipefail
cd "$(dirname "$0")"
echo "== checksums of out/"
shasum -a 256 -c SHA256SUMS --quiet
echo "== certificate audit (all remaining cases, sampled inflations, coverage of 20..20000, small tilings)"
python3 verify/audit.py .
echo "== Figure 1: Moron's rectangle with moved cut lines tiles R_32"
python3 verify/check.py out/illustr/moron_n32.txt 33 32
echo "== exhaustive search for n <= 19 (skyline search in C), compared with Theorem 1"
cc -O2 -o frame src/frame.c
solvable=" 4 10 12 14 15 18 "
for n in $(seq 1 19); do
  last=$(./frame $((n+1)) "$n" 1 $((n-1)) 0 1 | tail -n 1)
  count=$(printf '%s\n' "$last" | sed -n 's/^COUNT \([0-9]*\) .*/\1/p')
  [ -n "$count" ] || { echo "FAIL n=$n: no COUNT line ($last)"; exit 1; }
  case "$solvable" in *" $n "*) want=yes ;; *) want=no ;; esac
  got=no; [ "$count" -gt 0 ] && got=yes
  echo "n=$n $last  tiling: $got"
  [ "$got" = "$want" ] || { echo "FAIL n=$n: expected tiling $want"; exit 1; }
done
if python3 -c "import z3" 2>/dev/null; then
  echo "== independent exact-cover check for n <= 18 (n = 19 takes a few minutes: add 19 to run it)"
  python3 verify/small_sat.py $(seq 1 18)
else
  echo "(z3-solver not installed: skipping the independent exact-cover check)"
fi
echo "ALL CHECKS PASSED"
