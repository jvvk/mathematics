# Boomerangs in Pólya's orchard: how far a circular arc can see

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/079071eabf857b5cf4eae1107cea15f94bb73e2e/assets/boomerangs.svg" width="760" alt="Boomerangs in Pólya's orchard"></p>

<p align="center"><b>With trees of radius r at the lattice points, a circular arc from the origin can see farther than any straight line: between 4/r − 10 and 28/r². The true order of growth is open.</b><br><sub>Partial progress · bounds formally verified in Lean · arcs certified exactly</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Place an open disc of radius `r` at every nonzero lattice point. A straight line from the origin is blocked within distance about `1/r` (Pólya's orchard problem). On [MathOverflow 224015](https://mathoverflow.net/q/224015) (Joseph O'Rourke, 2015) the question is how far sight can reach along a **circular arc** from the origin. Call the answer `B(r)`.

**Theorem.** For `0 < r ≤ 1/10`,

`4/r − 10 < B(r) ≤ 28/r²`,

and the lower bound holds for all `r ≤ 1/3`.

The lower bound comes from an arc that threads the corridor between the first two columns of trees, staying between `x = r` and `x = 1 − r`. The upper bound combines Minkowski's theorem for nearly straight arcs with a corridor lemma for lattice lines of every slope and the spacing of Farey directions. Arcs found by search and certified exactly reach farther:

| 1/r | 4 | 6 | 10 | 16 | 20 |
|---|---|---|---|---|---|
| certified reach | 9.909 | 18.980 | 43.793 | 111.682 | 151.995 |

The order of growth, somewhere between `1/r` and `1/r²`, is open.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The inequalities behind both bounds are formally verified in Lean 4 (`lean/`, standard axioms only); Minkowski's and Pick's theorems are cited. The arcs are certified by computing their first contact with a disc in 60-digit arithmetic, and an independent script checks them by dense sampling. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf`, the figures `fig_corridor.tex` and `fig_best.tex` and their generator `make_fig.py`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 11 mutation tests.
- `verify/`:
  - `certify.py`: the exact reach of an arc in 60-digit arithmetic; certifies `certificates.json`.
  - `check.py`: five claims (Theorem 1 numerically and geometrically, the table, the quoted ratios, the numerical upper bound, the constants of Theorem 2 on a grid), each with a mutant that is caught.
  - `orchard.py`, `scan2.py`: the search (exact blocked direction intervals for each arc radius, then polishing); `corridor.py`: corridor arcs; `bound.py`: a numerical evaluation of the upper-bound argument (not part of the proof).
  - `recheck/recheck.py`: an independent check of every certified arc and of corridor arcs by dense sampling.

## Reproduce

```
cd verify && python3 check.py                   # about 10 seconds; needs mpmath and numpy
python3 certify.py                              # about 3 seconds
cd recheck && python3 recheck.py                # under a second
cd ../../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
