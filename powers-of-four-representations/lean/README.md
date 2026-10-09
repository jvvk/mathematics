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
definition, hypothesis or constant and checks that the file no longer compiles.

| Paper | Lean (namespace `SandorYang`) |
|---|---|
| `D`, `G = (1 − x)⁻¹ − D`, `R_{A,h}(N) = [x^N] G^h`, `m(N)` | `Basic.lean`: `D`, `U`, `G`, `R`, `m` |
| `R_{A,3}` counts ordered triples | `Basic.lean`: `R_three_eq_card` |
| Identity (1) | `Basic.lean`: `key_identity` |
| Lemma 2 | `Basic.lean`: `diff_ge` |
| Lemma 3 (from `h = 3` to every `h ≥ 3`) | `Basic.lean`: `strictMono_of_three` |
| Proposition 1 | `Powers.lean`: `E4`, `m_E4_bound`, `R3_strictMono`, `R_strictMono` |

`R` is defined as a coefficient of a power series in `ℤ⟦X⟧`, as in Section 2 of the note;
`R_three_eq_card` checks that for `h = 3` this is the number of ordered triples from `A` with sum `N`.
For general `h` the identification is the standard expansion of `G^h`, used as in Sándor and Yang.

Not formalised: Propositions 4 (eventually periodic sets) and 5 (growth of `A(N)`), and Remark 6, which
is numerical evidence only. Every result uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
