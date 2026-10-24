# Lean proof sources

Lean 4.34.0; Mathlib is pinned by lake-manifest.json to
5ed2965256430c3649e86755f9576b54eca72435 (v4.34.0).
SOURCE-SNAPSHOT.json records the development commit and the hash of every file. Build caches are excluded.

    lake exe cache get
    lake build LeanProofs
    lake env lean CheckClaims.lean
    python3 scripts/mutants.py

The first command fetches the pinned Mathlib cache, the second compiles the proofs, the third prints the
statements and axioms of the results below, and the last runs the 63 mutation tests: each plants one wrong
constant, sign, hypothesis or statement and checks that the module no longer compiles.

| Paper | Lean file | Main theorems (namespace `Phyllotaxis`) |
|---|---|---|
| Lemma 2.2 (threshold law), the tiling `K₀`, Lemma 7.3 identities, `√(3/28)` | `Tilings.lean` | `Tilings.threshold_tan`, `Tilings.K0.height_gaps` |
| Lemmas 4.1, 4.4 (at `Q₀`), 4.5, 4.3 (notch); `μ_Z > 0` on valid fronts | `Static.lean` | `Static.notch60_tan`, `lattice_Q0`, `pentagon_first`, `notch_clear`, `channel_of_valid` |
| Local five-disk families: the hypotheses are satisfiable | `StaticExists.lean` | `StaticExists.front_exists` |
| Lemma 3.1 (the apex branch: differentiability at 0, tangency nearby and local uniqueness, not the full C¹-neighbourhood statement) and non-vacuity | `Apex.lean`, `Lemma4Exists.lean` | `Apex.apex_exists`, `Apex.rhombic_family_exists`, `Lemma4Exists.dG_dc_family`, `dG_dθ_family` |
| Lemmas 3.2, 3.3 and Corollary 3.4 | `FirstOrder.lean` | `FirstOrder.rhombic_step`, `triangle_step`, `cushion_rate` |
| The first-transition margin and `√7` | `FirstOrder.lean`, `Lemma4.lean` | `FirstOrder.split_rate`, `pass_rate`, `Lemma4.n1_exclusion` |
| Lemma 7.2 | `Lemma4.lean` | `Lemma4.dG_dc`, `dG_dθ`, `kappa2_eq`, `boundary_slope` |
| Lemma 5.1, the gap in Lemma 6.2 | `PassBalance.lean`, `Sweep.lean` | `pass_balance`, `pass_lag`, `sweep`, `alternation_gap` |
| Proposition 5.2 (frozen shape) | `Prop2.lean` | `Prop2.prop2` |

Rechecking a file establishes its encoded statement; equivalence to the geometric model rests on the hypotheses
stated in each file and in the paper's appendix. The local existence results in `Apex.lean` and
`StaticExists.lean` do not certify periodic closure or global placement order.

Not formalised (proved by hand in the paper): the uniform remainders (Lemma 3.5); the full periodic first-disk
argument of Theorem A, namely the ridge clearance (Lemma 4.3), the lattice order (Lemma 4.4), the separation of
`Z` and `E` and the exclusion of all other positions; the lattice-order argument in Lemma 7.1. The rational
candidate enumerations are certified in exact and interval arithmetic in `verify/`. The first-order burst
exploration does not prove Conjecture C. Every result above uses only propext, Classical.choice and Quot.sound
(axiom-validation.txt). The folder was compiled in an isolated build without the development cache
(build-validation.log).
