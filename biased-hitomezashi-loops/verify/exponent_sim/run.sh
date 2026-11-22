#!/bin/sh
# Regenerates big_<p>.txt (Question 6.4): 200 random 12000 x 12000 patterns at each p, fixed seeds,
# then fits local slopes. A few minutes on five cores. Run from this folder.
set -e
cc -O2 -o loops loops.c -lm
seed=1
for p in 0.5 0.4 0.3 0.2 0.15; do
  nice -n 15 ./loops 12000 "$p" 200 "$seed" > "big_$p.txt" &
  seed=$((seed + 1))
done
wait
python3 fit2.py | tee fit2-output.txt
