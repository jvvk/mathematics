# Lean formalisation: the elementary identities

Lean 4 with Mathlib, pinned by `lean-toolchain` and `lake-manifest.json`. The statements are in
`LeanProofs/Commutator84/Basic.lean`; `CheckClaims.lean` prints each statement and its axioms
(only `propext`, `Classical.choice`, `Quot.sound`; see `axiom-validation.txt`).

| Lean name | In the note |
|---|---|
| `choose_bridge` | the term-by-term identity in the proof of Lemma 3, `r s C(i,r) C(i,s) = i² C(i−1,r−1) C(i−1,s−1)` |
| `V_closed` | the endpoint count in Lemma 5, `Σ_a C(n,a) C(n,n−a) a! (n−a)! = 2^n n!` |
| `endpoint_sign` | Lemma 5, first count: the two unpaired flags have sign `−(−1)^n = +1` for odd `n` |
| `eliminate` | the proof of Theorem 1: the three identities force `(n+1)|F_n| = 2n·n!` |

Not formalised (argued in the note and checked by the two programs in `../verify/`): the Goupil–Schaeffer
formula in the form of Proposition 2 (a cited theorem of Chapuy, Féray and Fusy), the bookkeeping of Lemma 3,
the sign-reversing involutions of Section 4, and the two involutions and the insertion of Lemma 5.

Build: `lake exe cache get && lake build && lake env lean CheckClaims.lean`.
Mutation suite: `cd scripts && python3 mutate.py mutants.toml` (5 false variants of the statements above; all
rejected).
