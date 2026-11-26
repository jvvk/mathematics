# Lean formalisation: key lemmas

Lean 4 with Mathlib, pinned by `lean-toolchain` and `lake-manifest.json`. The statements are in
`LeanProofs/DescriptionTrees/Basic.lean`; `CheckClaims.lean` prints each statement and its axioms
(only `propext`, `Classical.choice`, `Quot.sound`; see `axiom-validation.txt`).

| Lean name | In the note |
|---|---|
| `Om` | the term `Ω(k, m)` |
| `Om_succ` | the recurrence of `Ω` in `k` (Step 3: the coefficient of `y^{k+1} z^m` in `𝓛H = 0`) |
| `Om_zero` | `Ω(0, m) = 1`, the start of that recurrence |
| `coeff_unique` | uniqueness in Step 3: the recurrence and the row `k = 0` determine the array |
| `lemma2_odd`, `lemma2_even` | Lemma 2, with `a_r`, `b_r` written with Mathlib's `ascPochhammer` exactly as in the `₃F₂` definition of `P_s` |
| `R`, `R_at_zero` | the quartic factor of Step 2 and `R(q, 0) = −zq` |
| `tStar`, `qStar`, `quartic_param` | the parametrisation (2) of Step 2 solves `R(q, t) = 0` |

Not formalised (exact SymPy certificates in `../verify/`, and the argument in the note): the catalytic
equation for actual trees (Step 1), the existence of the double root and the resultant factorisation
(Step 2), the identity `𝓛H = 0` and the passage from the differential equation to the coefficient
recurrence (Step 3), and Step 5.

Build: `lake exe cache get && lake build && lake env lean CheckClaims.lean`.
Mutation suite: `cd scripts && python3 mutate.py mutants.toml` (10 false variants of the statements above; all
rejected).
