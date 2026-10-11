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

| Paper (paper-arxiv, 6 Oct 2026)          | Lean                                                        |
|------------------------------------------|-------------------------------------------------------------|
| uniform measure on S²                    | `unif` (Sphere), `unif_eq_toSphere` = normalised `volume.toSphere` |
| Lemma 1 (angle test)                     | `angle_identity` (Count)                                    |
| Lemma 2 (criterion)                      | `acute_iff` (Geom)                                          |
| Table: common face, eq. (3), marks       | `threshold`, `marked_iff` (Count)                           |
| Lemma 3 (nonempty, ≤3 per line, ≤4)      | `restrictions` (Count); `exists_short`, `no_star`, `one_per_face` |
| Lemma 4 (N + C = 4)                      | `count_eight`, `count_sixteen` (Count)                      |
| E N = 8p, p = 1/2 − P(k ∈ {1,2})         | `count_integrated` (Prob)                                   |
| eq. (5) moments                          | `moments_integrated` (Prob)                                 |
| Archimedes                               | `vol_cone` (Cone), `unif_le`, `unif_lt`, `unif_eq_zero` (Sphere) |
| q = (2 − s)/4, ⟨a,b⟩ uniform             | `q_eq`, `law_inner` (Pair)                                  |
| α = 1/6, γ = 1/24                        | `alpha_eq`, `gamma_eq` (Pair); `PP_Fl`, `PP_Fl_inter` (Prob) |
| null-set convention                      | `ae_generic` (Prob)                                         |
| p = 1/12                                 | `prob_all_faces_acute` (Prob)                               |

Not formalised: the closing remarks of the paper (the example in `ℝ⁴` and the comparison of counting formulas).

Every result uses only propext, Classical.choice and Quot.sound (axiom-validation.txt). The folder was
compiled in an isolated build without the development cache (build-validation.log).
