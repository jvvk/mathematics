# Numerics (not certified)

Exploration behind Table 2, Figure 2 and the remark on the maximal monotone correlation. These use floating point and
a local optimiser with restarts; their outputs are upper bounds for the least number of categories, not proofs. The
only certified number in the paper is Proposition 5.1 (`../certify_arb.py`, `../independent_check.py`).

- `intscores.py`: implied correlation of integer scores for given cut-points (Lemma 2.1) and a BFGS optimiser over
  cut-points.
- `regression.py`: closed form of `E[V | U = u]` (Proposition 3.1); `python3 regression.py` compares it with quadrature.
- `table.py`: least `m` with inflation for several `rho_S` (`mstar.out`, Table 2) and the data of Figures 1 and 2
  (`fig_reg_t3.dat`, `fig_reg_t10.dat`, `fig_gap_t10.dat`). About 20 minutes.
- `svd.py`: top singular value of an equiprobable `N x N` Frank table against `rho_S` (lower bound for the maximal
  monotone correlation; 0.863325 at theta = 10, N = 400).

Run from this folder: `python3 table.py`, `python3 svd.py`.
