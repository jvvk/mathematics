# Lean formalisation: cycles of length 2^n − 2 in the de Bruijn graph

Lean 4.34.0 with Mathlib v4.34.0. Build with `lake exe cache get && lake build LeanProofs`, then
`lake env lean CheckClaims.lean` prints each result's axioms (only `propext`, `Classical.choice`,
`Quot.sound`). `python3 scripts/mutants.py` checks that 9 wrong variants fail.

Vertices of `B(m)` are residues mod `2^m` with edges `u → 2u + b`; the alternating vertices are `p = −1/3` and
`q = −2/3` (`pv`, `qv`); `P` is the walk matrix over `ℚ`, `J` the all-ones matrix, `w = e_p − e_q`.

| Paper | Lean (namespace `DeBruijnCycles`) |
|---|---|
| Lemma 1, as: the only balanced two-edge deletions are the two loops and the alternating 2-cycle | `balanced_pairs` |
| Case A: deleting the loops leaves the Laplacian unchanged | `caseA`, `lap_delete_loop` |
| `L' = L − w wᵀ` for the 2-cycle | `lap_delete_two_cycle`, `lap_debruijn`, `adj_pq`, `adj_qp` |
| Lemma 3: `P^k(u,v) = 2^{-k}·#{c < 2^k : v = 2^k u + c}`, and `P^m = J/2^m` | `pow_P`, `pow_P_self`, `powP_self_eq` |
| Returns of the walk at `p` and `q` (parity) | `cnt_pp`, `cnt_pq`, `powP_compl` |
| `wᵀ P^k w = 2(−1/2)^k` for `k < m` | `quad_powP` |
| `(I − P) Z = I − J/2^m`, `(L + J) y = w` | `one_sub_P_mul_Z`, `LJ_mulVec_y` |
| `det(L + J − wwᵀ) = det(L + J)(1 − wᵀy)` | `det_rank_one` |
| `1 − Σ_{k<m} (−1/2)^k = (2^{m−1} + (−1)^m)/(3·2^{m−1})` | `w_dot_y`, `ratio` |
| Case B: the determinant ratio for `B(n+1)` | `caseB` |
| Closed forms for case B and the total | `caseB_closed`, `total_closed` |

## What is not formalised

The BEST theorem, Tutte's matrix-tree theorem (in the form: arborescence count `= det(L + J)/N²` for a matrix
with zero row and column sums; the cofactor identity is Lemma 2 of the note, proved there), the de Bruijn count
`2^(2^m − m − 1)`, and the correspondence between cycles of `B(m+1)` and closed trails of `B(m)`. These are
standard and are cited in the note.
