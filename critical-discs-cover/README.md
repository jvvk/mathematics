# Critical random discs cover the disc

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/22291349dac5b0d080c891a2d40ee8fd076144b3/assets/critical-discs-cover.svg" width="760" alt="Critical random discs cover the disc"></p>

<p align="center"><b>Discs of areas π, π/2, π/3, … with uniform centres cover the unit disc almost surely, assuming Zhou's new criterion for the interior; the rim follows from Shepp's theorem.</b><br><sub>Answers a question conditionally · analytic core in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Place discs of areas `π, π/2, π/3, …` with independent centres uniform in the closed unit disc. Are they sure to cover it? MathOverflow [question 458793](https://mathoverflow.net/q/458793) asks this. The areas are exactly critical: with areas `cπ/n` the uncovered set has dimension `2(1 − c)`, and at `c = 1` the known sufficient conditions (Biermé and Estrade, 2012) do not decide it.

**Theorem (conditional).** Assuming Zhou's exact criterion for random ball coverings of tori (arXiv:2609.02156, September 2026, not yet refereed), the unit disc is covered almost surely.

The interior reduces to Zhou's criterion on a torus of area `π` by a measure-preserving localisation. The criterion holds because two unit discs at distance `s` overlap in a lens that contains the disc of radius `1 − s/2` about their midpoint, so `H(t) ≥ 2 log(1/t) − log π − 2` and `∫ e^H` diverges. The boundary circle needs only Shepp's theorem: conditionally on their lengths the arcs have uniform positions, the mean of Shepp's function grows like `log(1/t)`, and Chebyshev and Borel-Cantelli control the fluctuations.

Preprint v1, 12 October 2026, not peer reviewed; conditional on Zhou's criterion for the interior. The analytic estimates are formally verified in Lean 4 (`lean/`, standard axioms only): the lens bound, the lower bound for Zhou's function with the harmonic and square-root sums behind it, the divergence, and the rim sliver estimate. Zhou's criterion, Shepp's theorem, the localisation and the probabilistic estimates are not formalised. The author used AI tools (Claude, Anthropic), as stated in the paper, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `verify/verify.py`: evaluates `H(t) − 2c log(1/t)` and `E F(t) − c log(1/t)` for `t` from `10^-1` to `10^-3.5`; for `c = 1` both level off (prints `LEVELS OFF`), and `python3 verify.py 0.9` must print `DRIFTS`. Numerical illustration, not proof.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 verify.py && python3 verify.py 0.9 | tail -1
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
