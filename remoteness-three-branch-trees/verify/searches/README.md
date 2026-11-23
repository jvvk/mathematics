# Searches behind Remark 3.5 (no counterexample in these ranges)
Each run tests every multiset D of k segment lengths, each at most L, over every D-tree (every series-reduced
skeleton and every distinct assignment), using ../remote.py.
- `analyze.py 3 7 10` -> `analyze_k3-7_L10.jsonl`: all D with 3 <= k <= 7, lengths <= 10, one record per D; field
  `nbs` lists the branch-vertex counts of all minimisers. No record has every minimiser with >= 3 branch vertices.
- `sweep.py k L` -> `sweep_k{k}_L{L}.txt` (summary lines): k = 7, L <= 15; k = 8, L <= 9; k = 9, L <= 5;
  k = 10, L <= 3 (plus smaller ranges). "strong 0, weak 0" means no D has a minimiser with >= 3 branch vertices.
