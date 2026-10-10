# Raising the apex raises the Gaussian centroid

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/bfa08660fa876dbcade1681f9f0956496aafa5b8/assets/raising-apex.svg" width="760" alt="Raising the apex raises the Gaussian centroid"></p>

<p align="center"><b>Raise a triangle's apex along the perpendicular through a point of its base and the Gaussian centre of mass rises, in every dimension and wherever the Gaussian is centred; whether it always pins down the moving vertex is open.</b><br><sub>Partial progress · the steps after Prékopa's theorem formally verified in Lean · oblique case open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

jens asked on MathOverflow ([question 499635](https://mathoverflow.net/q/499635)) whether the centre of mass of the standard Gaussian restricted to a triangle `ABC` determines `C` once `A` and `B` are fixed, and needs the same for `n`-simplices. When neither triangle contains the other a separating line settles it; the hard case is when one contains the other.

**Theorem.** Let `K` be a compact convex set with nonempty interior in a hyperplane `H` of `ℝⁿ`, `D ∈ K`, and `T_h` the convex hull of `K` and the apex `D + hν` on the normal through `D`. Under the standard Gaussian restricted to `T_h`, the mean distance from `H` is strictly increasing in `h`.

So the Gaussian centroid determines the apex on every line perpendicular to a side (or facet) through a point of it: a family of nested triangles and simplices. The Gaussian may be centred anywhere. Every horizontal slice of `T_h` is the base scaled about `D`, so the height of a Gaussian point has density `w(y) F(1 − y/h)` with one function `F`, the Gaussian mass of the scaled base. Prékopa's theorem makes `log F` concave, and a concave increasing function gains more over longer, lower intervals; so the likelihood ratio between two apex heights increases, the vertical factor `w` cancels, and Chebyshev's integral inequality raises the mean. Both hypotheses matter: with the foot outside the base the mean height can fall. When the apex moves obliquely the slices are no longer scaled copies about one point and the argument stops: the general question is open.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The steps after Prékopa's theorem (the cone lemma, the increment lemma, the monotone likelihood ratio, Chebyshev's integral inequality with its strict form, the mean comparison) are formally verified in Lean 4 (`lean/`, standard axioms only); Prékopa's theorem and the Gaussian factorisation are quoted. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure `fig_slices.tex` and `make_fig.py`, which computes the centroids it shows.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names and lists what is quoted, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 9 mutation tests.
- `verify/`:
  - `check.py` asserts every number in the note (the foot-outside heights 5.050 and 4.048, the exact `−35/6`, the figure's centroid heights by Gauss–Legendre quadrature); four mutants are rejected.
  - `verify.py`: 477 assertions auditing the section identities, likelihood ratios, means, a tetrahedron, and boundary and shape-derivative identities used in the (open) general case; `run_checks.py` runs it and nine deliberate mutations, all rejected.
  - `recheck/recheck.py`: an independent check sharing no code with the rest: Monte Carlo on Gaussian points for the figure, three more feet and centres, a tetrahedron over a non-symmetric base, and the foot-outside example by importance weighting; three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 check.py && python3 run_checks.py    # a few seconds; needs NumPy and SymPy
python3 recheck/recheck.py                   # a few seconds; needs NumPy
cd ../paper && python3 make_fig.py && latexmk -pdf note.tex    # make_fig.py needs SciPy
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
