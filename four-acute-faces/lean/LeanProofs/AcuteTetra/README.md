# AcuteTetra: "Four Acute Faces" (MO 498296), formalised

Main theorem (`Prob.lean`):

    theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 12)

`PP` is the law of four independent uniform points on the unit sphere of `EuclideanSpace ℝ (Fin 3)`;
`AllFacesAcute A` says every angle of every face is acute. Axioms: `propext`, `Classical.choice`,
`Quot.sound` only. Mutation tests: `scripts/mutants_acutetetra.sh` (all mutants rejected).

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

Not formalised: the remarks in §7 (the R⁴ orthonormal example, the N = 4 − 2m + J comparison).
