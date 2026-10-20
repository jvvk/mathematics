# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 12 mutation tests: each plants a false
statement or corrupts the data and checks that the files no longer compile.

**Main theorem** (`Main.lean`, `SpectreCover.spectre_twelve_fold`): for the 54 placements of the paper and every
vector of the period lattice, almost every point of the plane lies in exactly 12 tiles, each tile being a rigid
image of the straight-edged Spectre `Tile(1,1)`.

| Paper | Lean (namespace `SpectreCover`) |
|---|---|
| The indicator of a triangle as a sum of signed edge shadows | `Shadow.lean`: `tri_shadow` |
| A periodic triangle family whose edges cancel modulo the lattice has a count constant along vertical lines, and almost everywhere | `Cover.lean`: `vmove`; `Ae.lean`: `cnt_ae_const` |
| Section 4: the count times the cell area equals the total area | `Count.lean`: `count_mul_det` |
| The Spectre in `ℤ[ζ]`, its triangulation and the 54 placements; kernel certificates: triangle edges cancel, the triangulation's boundary is the 14-gon, placements are distinct | `Data.lean`: `keys_sorted_eq`, `tris_boundary`, `placements_injective` |
| Lemma 2 for curved Spectres: the 378 + 378 curved-edge records cancel | `Data.lean`: `curved_records_cancel` |
| Every triangle is counterclockwise; the family meets every hypothesis; `det(v, w) = (27/2)(1 + √3)` | `Concrete.lean`: `all_ccw`, `V_paired`, `det_eq` |
| The constant is 12; tiles are unions of their triangles, which do not overlap | `Main.lean`: `sum_orient`, `cnt_ae_twelve`, `tile_eq`, `tiles_separated` |
| Theorem 1 for `Tile(1,1)` | `Main.lean`: `spectre_twelve_fold` |

The finite certificates are checked by `decide +kernel` (no `native_decide`).

Not formalised: for curved Spectres, the step from the cancelling curved-edge records to constant coverage,
which needs the Jordan curve theorem for the edge curve. Minimality of 12 is not claimed. Every result above
uses only Lean's standard axioms or a subset of them (axiom-validation.txt). The folder was compiled in an
isolated build without the development cache (build-validation.log).
