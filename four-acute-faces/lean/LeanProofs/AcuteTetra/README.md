# AcuteTetra: "Four Acute Faces" (MO 498296), formalised

Main theorem (`Prob.lean`):

    theorem prob_all_faces_acute : PP {A | AllFacesAcute A} = ENNReal.ofReal (1 / 12)

`PP` is the law of four independent uniform points on the unit sphere of `EuclideanSpace ℝ (Fin 3)`;
`AllFacesAcute A` says every angle of every face is acute. Axioms: `propext`, `Classical.choice`,
`Quot.sound` only. Mutation tests: `scripts/mutants_acutetetra.sh` (all mutants rejected).

The map from the paper to the Lean names is in `lean/README.md` at the top of this folder.

Not formalised: the remarks in §7 (the R⁴ orthonormal example, the N = 4 − 2m + J comparison).
