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
statement, constant or point and checks that the file no longer compiles.

**Scope.** The Brunn–Minkowski inequality and the isodiametric inequality are not in Mathlib. The paper
quotes them (Gardner, Bull. Amer. Math. Soc. 39, 2002); Lean proves everything Theorem 1 does with their
output. Batominovski's point colouring (Theorem 4) is a retelling of the accepted answer, and only its
geometric lemma is formalised.

| Paper | Lean (namespace `SevenColours`, file `Basic.lean`) |
|---|---|
| Lemma 3 (and its strict form below `30°`) | `thirty`, `thirty_strict` |
| `A/(√A + c)²` increases with `A` | `ratio_mono` |
| The density bound `(π/4)/(√π/2 + √(3π)/2)² = 1/(1 + √3)²` | `density_eq` |
| `1/(1 + √3)² < 1/7` | `density_lt` |
| Theorem 1: `k` classes of that density cover the plane only if `k ≥ 8` | `colours_ge_eight` |
| Section 4: the two witness points, their hexagons and their distance | `hexagon_counterexample` |

`thirty` takes `cos θ ≥ √3/2` for an angle `θ ≤ 30°`. `hexagon_counterexample` checks that the two hexagons'
centres differ by `a = 3x − y`, which lies in the sublattice that defines the colouring.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
