# Lean formalisation: the finite identities

Lean 4 with Mathlib, pinned by `lean-toolchain` and `lake-manifest.json`. The statements are in
`LeanProofs/Slit236/Basic.lean`; `CheckClaims.lean` prints each statement and its axioms
(only `propext`, `Classical.choice`, `Quot.sound`; see `axiom-validation.txt`).

| Lean name | In the note |
|---|---|
| `balanced_stop` | Lemma 5, balanced words: `∑_{k=1}^{r} 2·C(2r−k−1, r−1) = C(2r, r)` (indexed by `j = r − k`, `r = s + 1`) |
| `return_count_step` | Lemma 5, `2r·C(2r−k, r) = 2(2r−k)·C(2r−k−1, r−1)`, the step from the forest count to the stopping-time sums |
| `endpoint01` | Section 5, proof of 236(a): Corollary 7, Lemma 9, the closing step and Proposition 8 force `a_{0,1}(2n+1) = H_n` |
| `binom_236d` | Section 6, 236(d): `C(4n, 2n−2)/(2n) = C_{2n+1}/2 − C_{2n}` for `n ≥ 1` |
| `endpoint11` | Section 6, 236(d): the elimination giving `2a_{1,1}(2n) = H_n/2 + C_{2n}` |
| `cycle_weight_237d` | Section 7, 237(d): a decorated-bridge cycle has weight `c_d(r, 2j) = 4^r/(2r)·C(2r, r+j)` |
| `count_237d` | Section 7, 237(d): the decorated bridges number `(i/n) C(2i,i) C(2n,n−i) 4^(n−i)` |
| `diagonal_sum` | Section 7, 237(b): the closing step gives `b_{1,1} + b_{−1,1} = 2·4^n C_n` |
| `diag_237b` | Section 7, 237(b) from 237(a) |

Not formalised (argued in the note and checked by the programs in `../verify/`): the cycle-sorting bijections
(Lemma 3) and the counting formula (Lemma 4), the free-word count `∑ 2^(k+1) C(2r−k−1, r−1) = 4^r` of Lemma 5, the
marking argument and the pair-splitting sum of Lemma 6, the sign-reversing involutions of Proposition 8 and Lemma 9,
and Shapiro's identity (a cited theorem; bijective proof by Hajnal and Nagy).

Build: `lake exe cache get && lake build && lake env lean CheckClaims.lean`.
Mutation suite: `cd scripts && python3 mutate.py mutants.toml` (9 false variants of the statements above; all
rejected).
