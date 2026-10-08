# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the headline results, and the last runs the mutation tests: each plants one wrong
constant, hypothesis or definition and checks that the file no longer compiles.

| Paper | Lean |
|---|---|
| The process (zero-padded rows, independent coins, expectation by the Markov property) | `Basic.lean`: `cell`, `step`, `Valid`, `P`, `Exp` |
| Independence of three coins; summing over windows | `Sums.lean`: `marg3`, `sum_shift`, `P_window` |
| Lemma 1 | `TheoremA.lean`: `P_S` |
| Lemma 2 | `TheoremA.lean`: `E3_jump`, `P_V` |
| Theorem 1 | `TheoremA.lean`: `theoremA`, `one_lt_lamA` |
| The local inequality (2) and the window identities of Section 5 | `TheoremB.lean`: `Gloc`, `LocalIneq`, `sum_Iloc`, `sum_Oloc` |
| Theorem 2, given (2) | `TheoremB.lean`: `theoremB`, `theoremB_quarter` |
| `Gloc` agrees with the certificate program at five points | `Bridge.lean`: `bridge1` to `bridge5` |
| L_p = infinity | `Mean.lean`: `meanN_diverges_A`, `meanN_diverges_B` |

Theorem 1 and its corollary are proved outright. Theorem 2 takes the local inequality `LocalIneq mainCert p`
as a hypothesis; that inequality is established by the exact certificate in `../verify`, not in Lean.
Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
