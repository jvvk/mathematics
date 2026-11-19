#!/bin/bash
# Build the Lean modules one at a time, then print every claim and its axioms.
# A plain `lake build` compiles the case-split files in parallel; each needs up to ~10 GB, so on a
# laptop that can exhaust memory.
set -uo pipefail
export LEAN_NUM_THREADS=1
cd "$(dirname "$0")"
mods="LeanProofs.Shuffle LeanProofs.ShuffleW.Defs"
for i in $(seq -w 0 12); do mods="$mods LeanProofs.ShuffleW.Cut$i"; done
mods="$mods LeanProofs.ShuffleW LeanProofs.ShuffleU LeanProofs.ShuffleBlocks.Basic"
for i in $(seq -w 0 9); do mods="$mods LeanProofs.ShuffleBlocks.Cut0${i: -1}"; done
mods="$mods LeanProofs.ShuffleBlocks LeanProofs"
for m in $mods; do
  echo "== $m $(date +%H:%M:%S)"
  nice -n 15 lake build "$m" > "logs_${m}.log" 2>&1 || { echo "FAIL $m"; tail -20 "logs_${m}.log"; exit 1; }
done
echo build=0
nice -n 15 lake env lean CheckClaims.lean
