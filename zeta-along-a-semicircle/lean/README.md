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
statement or hypothesis and checks that the file no longer compiles.

**Scope.** The proof is computer assisted. Lean checks the exact reductions that turn ball-arithmetic
enclosures into a proof; the enclosures of `ζ`, `ζ'`, `ζ''` (Arb, through python-flint), the averaging
argument near the start and the formula for `R'` are outside Lean.

| Paper | Lean (namespace `ZetaArc`, file `Basic.lean`) |
|---|---|
| Section 2: `Re(z'/(z - z₀)) = (1/2) cot(u/2)` for `z = 1 - r e^{iu}`, `z₀ = 1 - r` | `re_ratio` |
| Section 2: `ζ'/ζ = 1/(z - z₀) + h'/h` for `ζ = (z - z₀) h` | `log_deriv_split` |
| Equation (1): `(1/2) cot(u/2) > r M` and `|h'/h| ≤ M` give `R > 0` | `region_a` |
| Section 2: `R(π) = 0` (`z' = r i`, real values at `1 + r`) | `R_pi` |
| Section 2: `R' < 0` on `(a, π)` and `R(π) = 0` give `R > 0` on `[a, π)` | `pos_of_deriv_neg` |

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
