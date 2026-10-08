# Lean formalisation: Random chords of two circles and a third centre

Lean 4 (v4.34.0) with Mathlib `v4.34.0`: every proved result of the paper (`../paper/paper.tex`),
along its route. Angles live on `ℝ ⧸ 2πℤ` with Haar measure; a law is a push-forward of `volume`
on `Ang × Ang` (mass `4π²`), so equality of laws is equality of push-forwards. Every result depends
only on `propext`, `Classical.choice` and `Quot.sound` (`Audit.lean`).

| Paper | Lean | File |
|---|---|---|
| Notation: points, unit normal `m` with `0 < φ < π`, offsets `x_A, x_B`, distance to a line | `pt`, `nrm`, `off`, `lineDist` | `Basic.lean` |
| "Summing the contributions": law of an angle map from finitely many inverse branches | `map_eq_of_branches` | `Branches.lean` |
| Lemma 1 (`φ` uniform, `x_B` arcsine, independent) | `lemma1` | `OneCircle.lean` |
| Lemma 2, the four pairs, `∂φ/∂θ_A = u/g`, `∂φ/∂θ_B = -v/g`, determinant `1 + εu/g - ηv/g` | `psi2`, `hasFDerivAt_phi`, `det_psi2'`, `jac_eq` | `TwoCircles.lean` |
| The gaps are non-negative (disjoint chords); the four contributions add to `4` | `half_chords_le`, `jac_nonneg`, `sum_jac` | `TwoCircles.lean` |
| **Lemma 2** (angle form; offset form) | `lemma2`, `lemma2_offsets` | `TwoCircles.lean`, `Offsets.lean` |
| Remark after Lemma 2: the law of the direction of `AB` | `direction_law` | `Offsets.lean` |
| Lemma 3 (support end and second moment determine the weights) | `lemma3` (with `sum_abs_eq_of_lawW_eq`, `second_moment`) | `Moments.lean` |
| Projection identity (T) | `dAB_eq`, `dBC_eq` | `Centres.lean` |
| **Theorem 4**, and the common law `|b cos U - |QO| cos V|` | `theorem4`, `law_dBC'` | `Centres.lean` |
| Corollary 5 (Dan and Tom Sirgedas, every ratio; converse) | `cor5`, `cor5_hit` | `Corollaries.lean` |
| Theorem 4 with the circles exchanged; Corollary 6 (chains) | `theorem4_mirror`, `cor6` | `Corollaries.lean` |
| Corollary 7 (formula; continuous, strictly increasing, limits 0 and 1) | `H_formula`, `H_continuousOn`, `H_strictMonoOn`, `H_tendsto_zero`, `H_tendsto_one`, `hit_eq_H` | `HitProb.lean` |
| Corollary 8 (Dan's constant as an arccos integral) | `cor8` | `HitProb.lean` |
| Remark: disjointness is needed (concentric circles) | `concentric` | `Remarks.lean` |
| Remark: the off-axis identity (2), the necessary condition, the perpendicular displacement, the `0.02` example | `offaxis_moment`, `offaxis_necessary`, `offaxis_perp`, `offaxis_example` | `Remarks.lean` |

Not formalised: the numerical value `0.38712871…` of Corollary 8 and its agreement with Dan's
dilogarithm expression (computed by the ancillary scripts), and the classical formula of Santaló cited
after Lemma 2 (a remark; the proof of Lemma 2 does not use it).

`./mutants.sh` plants 23 wrong changes (definitions, statements and hypotheses across
every file) in a copy of the sources; each must fail to build, and the unchanged copy must build.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit
./mutants.sh           # 23 mutants, each rejected; the unchanged copy builds
```
