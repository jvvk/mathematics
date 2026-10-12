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
constant, hypothesis or statement and checks that the file no longer compiles.

Main theorem (`Prob.lean`):

    theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 12)

`PP` is the law of four independent uniform points on the unit sphere of `EuclideanSpace ℝ (Fin 3)`, and
`AllFacesAcute A` says every angle of every face is acute.

| Paper                                     | Lean                                                         |
|-------------------------------------------|--------------------------------------------------------------|
| uniform measure on the sphere             | `unif`, `unif_eq_toSphere` (Sphere)                          |
| Lemma 1 (angle test)                      | `angle_identity` (Count)                                     |
| Lemmas 2 and 3 (grid, criterion)          | `acute_iff` (Geom); `angle_edge`, `edge_angle` (Facts)       |
| Lemma 4 (threshold)                       | `threshold`, `marked_iff` (Count)                            |
| Lemma 5 (i), (ii), (iii)                  | `one_per_face`, `no_star` (Geom); `exists_short` (Main)      |
| count (2), in the form N + C = 4          | `count_eight`, `count_sixteen` (Count); `comb` (Comb)        |
| E N = 8p and the averaged count           | `count_integrated`, `moments_integrated` (Prob)              |
| Archimedes' theorem                       | `vol_cone` (Cone); `unif_le`, `unif_lt` (Sphere)             |
| cap probability (1 - s/2)/2               | `q_eq`, `law_inner` (Pair)                                   |
| alpha = 1/6, gamma = 1/24                 | `alpha_eq`, `gamma_eq` (Pair)                                |
| null events                               | `ae_generic` (Prob)                                          |
| p = 1/12                                  | `prob_all_faces_acute` (Prob)                                |

The formal proof follows the same plan as the paper but takes different routes in places. It proves
the count as N + C = 4, where C = 2m - J is the number of tetrahedra with one or two short faces, by an
exhaustive check over the patterns of short triangles allowed by its restriction lemmas, rather than
through the staircase.

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
