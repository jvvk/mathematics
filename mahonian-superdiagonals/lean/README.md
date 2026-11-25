# Lean formalisation: what is and is not proved

Lean 4 + Mathlib, namespace `Mahonian`, files in `LeanProofs/Mahonian/`. Build: `lake exe cache get && lake build`;
`lake env lean CheckClaims.lean` prints the axioms of every result below (recorded in `axiom-validation.txt`). Axioms of
every result below: propext, Classical.choice, Quot.sound. No sorry, no native_decide.

Everything is stated in `PowerSeries ℤ` and `Polynomial ℤ` without division: `geom = 1/(1-X)`, Euler's coefficients
`f s` read off the finite product `∏_{j≤s}(1-X^j)` (stability: `coeff_E_stable`), `A n k = [q^k] F·geom^n`,
`Aneg r k = [q^k] F·(1-X)^r`, `Cinv = 1 - X·C` with `Cinv_mul_Cat : Cinv * Cat = 1`, and `P i` written exactly as the
display in Theorem 1 of the note.

## Proved
| Note | Lean | Scope |
|---|---|---|
| (2) and Lemma 2, truncation | `mahonian_coe`, `Q_trunc`, `A_eq_trunc`, `I_split`, `lemma2` | all n; `A(n,k) = I_n(k) - ∑_{n<m≤k} I_n(k-m)` for k ≤ 2n+2 |
| Lemma 2: `c_n = 0` for `n ≥ i-1` | `c_eq_zero` | all i, n |
| Lemma 2: `c_{i-2} = 1` | `c_sub_two` | all i ≥ 2 |
| `I_n(n) = A(n,n)`, so `S_0 = ∑ A(n,n)x^n` | `I_diag`, `S0_eq_diag` | all n |
| Lemma 4 | `lemma4` | all t |
| Theorem 1, identity (1) with the explicit `P_i` | `main` | all i, given `H3 i` (below) |
| Theorem 1, degree | `natDegree_P`, `leadingCoeff_P` | all i ≥ 2: degree 3i-2, leading coefficient (-1)^i |
| Examples | `P_one`, `P_two` | `P_1 = -1 + 2x`, `P_2 = -1 + 4x - 4x^2 + x^3 + x^4` |

## Not formalised
- **Lemma 3** (Lagrange inversion for Laurent series, Gessel, J. Combin. Theory Ser. A 144 (2016), Theorem 2.1.1,
  eq. (2.1.4), with `R = 1/(1-t)`, `ψ(t) = t^{-i}F(t)`). It is the hypothesis `H3 i` of `main`, in Laurent-free form:
  `X^i * (mk fun n => A n (n+i)) + ∑_{r=1}^{i} C (Aneg r (i-r)) * X^(i-r) = Cinv^i * S0`.
  `H3 i` is true by Gessel's theorem (the note's Lemma 3); its coefficients also agree numerically with a separate
  program for i = 0..8 through x^39. That check is evidence for the encoding, not a proof of `H3`.
- The combinatorial meaning of the Mahonian numbers: `mahonian n` is defined as the generating polynomial
  `∏_{j<n}(1 + q + ⋯ + q^j)`; that its coefficients count permutations by inversions is classical and not formalised.
- Route difference: the note's Lemma 2 expands `∏_{j>n}(1-q^j)^{-1}` as a partition series. The Lean proves the
  equivalent inverse relation from `∏_{j=n+1}^{n+d}(1-X^j) ≡ 1 - ∑ X^m (mod X^{2n+3})`, avoiding infinite products.
  The note's Lemma 4 reads coefficients of `(1-q)/(1-x-q)`; the Lean uses the column recurrence
  `(1-x)·col_{u+1} = col_u - [u=0]`. Both prove the same statements.

## Mutation tests
`scripts/mutants.toml`, run with `cd scripts && python3 mutate.py mutants.toml` (runner included): 8 mutants, all
rejected, all controls pass. Each is a false version of a stated result: the truncation range (k ≤ 2n+5; at 2n+3 and 2n+4 the extended statement is still true, so those are not used), the
vanishing range of `c_n` (from i-2), `c_{i-2} = 2`, an exponent in Lemma 4, the main term `C^{-(i+1)}`, degree 3i-1,
leading coefficient (-1)^(i+1), and `P_1 = -1 + 3x`.
