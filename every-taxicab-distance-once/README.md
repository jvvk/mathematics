# Every taxicab distance once

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/taxicab.svg" width="760" alt="Eleven points, distances 1 to 55"></p>

<p align="center"><b>Eleven lattice points whose 55 taxicab distances are exactly 1 to 55; with the parity count (n or n − 2 a square), placements exist for every allowed n ≤ 15.</b><br><sub>Partial answer · parity count and n = 11 in Lean; n ≥ 16 open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Elliott asked on Mathematics Stack Exchange ([question 4967838](https://math.stackexchange.com/q/4967838)) for which `n` there are `n` points of the integer grid whose `N = n(n−1)/2` taxicab distances are `1, 2, …, N`, each exactly once. On a line this asks for a perfect Golomb ruler (a graceful labelling of `K_n`), which exists only for `n ≤ 4` (Golomb, 1972). The asker proved that `n` or `n − 2` must be a perfect square, and found placements for `n = 2, 3, 4, 6, 9`.

- **Theorem 1 (parity count).** With `a` points of even `x + y` and `b` of odd `x + y`, `(a − b)² = n` when `n ≡ 0, 1 (mod 4)` and `n − 2` otherwise. Odd distances are exactly the `ab` cross pairs, and `1, …, N` contains `⌈N/2⌉` odd numbers.
- **Proposition 2.** The eleven points `(0,14), (0,16), (1,16), (7,11), (8,7), (11,2), (12,7), (14,45), (17,49), (23,0), (23,26)` have taxicab distances `1, …, 55`, each once. A table in the paper lets a reader check this by hand.

So a placement exists for `n = 2, 3, 4, 6, 9, 11`, and for no other `n ≤ 15`. From `n = 16` on the question is open. The eleven-point placement was first posted as a Mathematics Stack Exchange [answer](https://math.stackexchange.com/a/5150779). Its picture lives in the separate repository [taxicab-distances-eleven](https://github.com/jvvk/taxicab-distances-eleven), which that answer links to.

Preprint v1, 10 October 2026, not peer reviewed. Theorem 1 and Proposition 2, including the colour split `7, 4`, are formally verified in Lean 4 (`lean/`, standard axioms only). The searches that found the placements are computations and stay outside Lean. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`. `figs/` holds the TikZ figure and table data written by `verify/fig_taxi.py` and `verify/fig_small.py`.
- `verify/`:
  - `taxi_check.py`: checks the parity rule against the square condition for `n ≤ 400`, and every placement in the paper with its colour split. `MUTANT=1` counts `⌊N/2⌋` odd numbers and `MUTANT=2` moves one point; each must print `FAIL`.
  - `perfect.c`: the exact search, which places distances from the largest down. It finds the placements for `n ≤ 6` and none for `n = 5, 7`. With the third argument `1` it skips one branch and must lose solutions.
  - `anneal.c`: the simulated-annealing search that found the placements for `n = 9` and `11`.
  - `fig_taxi.py`, `fig_small.py`: Figures 1 and 2 and Table 1. Each asserts that its placements realise every distance once.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 taxi_check.py && MUTANT=1 python3 taxi_check.py | tail -1 && MUTANT=2 python3 taxi_check.py | tail -1
cc -O2 -o perfect perfect.c && ./perfect 6 && ./perfect 7
cc -O2 -o anneal anneal.c -lm && ./anneal 11 60 1
python3 fig_taxi.py && python3 fig_small.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
