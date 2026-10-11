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
hypothesis, statement or constant and checks that the file no longer compiles.

**Scope.** Lean checks the arithmetic core of the paper. The geometric lemmas (diameter, vertex fan, four
half-planes), the analytic estimates of the rational-tangent lemma and the regional bounds of Theorem 1 are
proved in the paper and are not formalised; Observation 3 is certified in ball arithmetic by
`verify/largest_cell.py`.

| Paper | Lean (namespace `PolygonCells`, file `Basic.lean`) |
|---|---|
| Section 3: `b - a` and `b + a` are coprime (`a` odd, `b` even, `gcd(a, b) = 1`) | `coprime_sub_add` |
| Section 3: every level `b v - a u = k` contains a chord with `u ≡ v (mod 2)` | `lattice_exists` |
| Section 3: two chords on one level differ by a multiple of `(2b, 2a)` | `lattice_spacing` |
| Proposition 2: `R sin(t/2) = 1/(4 cos(t/2))` for `R = 1/(2 sin t)` | `inradius` |
| Proposition 2: `sin(3t/2) cos t - sin(t/2) = cos(3t/2) sin t > 0` for `0 < t < π/3` | `central_gap` |

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
