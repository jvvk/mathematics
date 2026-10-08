# Lean formalisation: Does the smallest enclosing copy fit?

Lean 4 (v4.34.0) with Mathlib `v4.34.0`. About 20,500 lines in two libraries:

- `EnclosingCopy/Poisson`: finite Poisson processes, void probabilities, the multivariate Mecke
  equation, superposition, infinite slab models, and the comparison of iid samples with Poisson
  processes on shrinking windows. Mathlib has no point processes, so all of this is built here.
- `EnclosingCopy/Enclosing`: the paper itself.

Every theorem below depends only on `propext`, `Classical.choice` and `Quot.sound`; `Main.lean`
prints the axioms of each one when it is compiled.

## Build

```
lake exe cache get     # Mathlib build cache
lake build             # compiles every module and runs the axiom audit in Main.lean
```

## Where each result is

| Paper | Lean | File |
|---|---|---|
| Theorem 1 (convergence, any strictly convex polygon of area one) | `theorem1`, `theorem1_model` | `Enclosing/Theorem1.lean` |
| Lemma 6 (tangent coordinates: exact containment and fit) | `mem_tangentCopyRegion_iff`, `exists_tangent_fit_radius` | `Enclosing/TangentSimilarity.lean`, `Enclosing/TangentFit.lean` |
| Step 0 (rotation localises) | `step0`, `step0_sample` | `Enclosing/Theorem1Step0.lean` |
| Step 1 (witnesses confine copies) | `finite_tangent_copy_bound`, `model_copy_bound` | `Enclosing/FiniteCoercivity.lean`, `Enclosing/Theorem1Model.lean` |
| Steps 2-3 (boundary window, Poisson approximation uniform over events) | `trueEv_iff_evN`, `polygon_boundary_uniform_error`, `polygon_boundary_varying_event_limit` | `Enclosing/Theorem1Physical.lean`, `Enclosing/UniformBoundary.lean`, `Enclosing/VaryingBoundaryLimit.lean` |
| Lemma 7 (nondegeneracy, via Mecke) | `nonDeg_ae`, `optimum_tilt_gap`, `strict_rep` | `Enclosing/Theorem1Strict.lean`, `Enclosing/Theorem1Model.lean` |
| Lemma 8 (stability) | `poisson_stable` | `Enclosing/Theorem1Events.lean` |
| Lemma 9 (void probability) | `void_area`, `model_void` | `Enclosing/Void.lean`, `Enclosing/Model.lean` |
| Theorem 10 (the formula), truncated and untruncated model | `general_optFit_limit`, `untruncated_prob` | `Enclosing/GeneralClassify.lean`, `Enclosing/Untruncated.lean` |
| Corollary 2 (triangles), 13/48 | `theorem1_triangle`, `theorem1_equilateral`, `g_closed` | `Enclosing/Theorem1.lean`, `Enclosing/Triangle.lean` |
| Corollary 3 (regular q-gons, every q >= 3) | `theorem1_regular`, `tetW_eq` | `Enclosing/Theorem1Regular.lean`, `Enclosing/Tetrahedron.lean` |

Each module begins with a comment describing what it proves.

Not formalised: the reduction to area one by scaling, the numerical values (simulations,
`p_q` for `q >= 5`, the triangle-shape scan) and the conjecture on the equilateral minimum.

## Mutation tests

Each script copies one source file, plants a single wrong change (a constant, a hypothesis, an
inequality) and checks that the result no longer compiles. Every planted mutant is rejected.

```
python3 scripts/enclosing_mutants.py                  # all paper-level mutants
python3 scripts/enclosing_mutants.py Theorem1Regular  # only those for one file
python3 scripts/enclosing_tangent_mutants.py          # the tangent-coordinate layer; likewise
                                                      # window, geometry, boundary, endpoint, area, uniform
```
