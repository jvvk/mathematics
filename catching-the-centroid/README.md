# Catching the centroid

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/94b3808cc162615b4da75b474ef30860491971b3/assets/centroid-circle.svg" width="760" alt="Catching the centroid"></p>

<p align="center"><b>A circle on a random diameter of a convex region contains the centroid with probability at most 14/27 ≈ 0.5185; the equilateral triangle's 0.5164 is conjectured best.</b><br><sub>Partial progress · bounds formally verified in Lean · sharp value open</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Pick two random points `X` and `Y` in a planar convex region `K` and draw the circle with diameter `XY`. Dan asked on Mathematics Stack Exchange ([question 5101873](https://math.stackexchange.com/q/5101873)) which convex shape makes this circle most likely to contain the centroid. A disc or a square gives exactly `1/2` and an equilateral triangle gives `1/3 + ln 3 / 6 ≈ 0.5164`; the answers there conjecture that the equilateral triangle is best. That conjecture is still open.

The note shows that the excess over `1/2` comes only from the asymmetry of `K` about its centroid. In polar coordinates about the centroid, `P(K) − 1/2` is the integral of the odd part of the angular density against the imbalance of the half-planes (Proposition 1), equivalently half the area swept by the imbalances of two perpendicular lines. Bounding it by the product of Grünbaum's half-plane asymmetry and the asymmetric share `1 − s(K)` of the region (Proposition 2), and using Stewart's 1958 theorem that `|K ∩ (2G − K)| ≥ (2/3)|K|` at the centroid `G`, gives:

- **Theorem 1.** `|P(K) − 1/2| ≤ 1/54` for every convex region, so `P(K) ≤ 14/27 ≈ 0.5185`, within `0.0021` of the conjectured value.

The note also gives a three-line proof of Stewart's inequality from Grünbaum's for regions whose boundary crosses its reflection through the centroid six times, which every region close to a triangle does (Lemma 1, Proposition 3), credits Levi's older bound `2/5`, and explains why `14/27` cannot reach `0.5164`: both factors of Proposition 2 are affine invariants, while `P` is not.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. Propositions 1, 2 and 3, formula (3), Lemma 1, Theorem 1 and the bound `8/15` are formally verified in Lean 4 (`lean/`, standard axioms only) for continuous periodic angular densities; Grünbaum's, Stewart's and the Minkowski–Radon inequalities are quoted and enter as hypotheses, and the polar-coordinate formula (1) is the Lean definition of `P`. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figure sources `fig_*.tex` and `gen_figs.py`, which writes them from the computed curves.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 14 mutation tests.
- `verify/`:
  - `core.py` (angular quadrature, Monte Carlo) and `exact.py` (polygon evaluators: `P` by adaptive quadrature in `tan`, robust on thin shapes; `|K ∩ (2G − K)|` by clipping).
  - `check.py`: controls against the asker's values and Monte Carlo, including thin and flat triangles, and numerical checks of Propositions 1 and 2 and formula (3); `mutants.py` checks that seven wrong variants of the evaluators fail it.
  - `table.py`: Table 1.
  - `searches.py`: every numerical claim of Sections 5 and 6 (`sharp`, `free`, `stewart`, `sided`, `shadow`, `steps`), each asserted; `stewart` checks Stewart's cap-by-cap inequality on 1500 random polygons.
  - `recheck/recheck.py`: an independent check sharing no code with the rest: Table 1, the asker's values, the figure captions, the arithmetic of Theorem 1 and the `8/15` bound, the count of three-sided polygons, Stewart's inequality on 500 random polygons, Monte Carlo agreement, and three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 check.py && python3 mutants.py
python3 table.py && python3 searches.py
python3 recheck/recheck.py
cd ../paper && python3 gen_figs.py && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

The Python programs need NumPy and SciPy. `searches.py` takes a few minutes on one core.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
