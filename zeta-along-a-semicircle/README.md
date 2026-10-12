# Zeta along a semicircle

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/6407e87d9d08d296acc2dac8ef775753fbcd2f9d/assets/zeta-along-a-semicircle.svg" width="760" alt="Zeta along a semicircle"></p>

<p align="center"><b>|ζ(z)| rises strictly along the semicircle from the trivial zero −4 to 6, and along the one from −2; along the semicircles through −6, −8, …, −40 it dips. Computer assisted in ball arithmetic.</b><br><sub>Answers a question · computer assisted · reductions in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Walk from the trivial zero `−4` of the Riemann zeta function to `6` along the lower semicircle `z = 1 − 5e^{iu}`, `0 ≤ u ≤ π`. Does `|ζ(z)|` increase all the way? Mathematics Stack Exchange [question 5150160](https://math.stackexchange.com/q/5150160) asks this, and whether a computer-assisted proof would count.

**Theorem 1.** For `r = 3` and `r = 5`, `|ζ(1 − re^{iu})|` is strictly increasing on `[0, π]`.

**Theorem 2.** For every odd `r` from 7 to 41, it is not monotone: `|ζ|` decreases on a certified interval.

The proof shows that `R(u) = d/du log|ζ(z(u))| = Re(z′ ζ′/ζ)` is positive. Near the start, `ζ = (z − z₀)h` and `Re(z′/(z − z₀)) = ½ cot(u/2)` dominates. Near the end `R(π) = 0` exactly, by symmetry, and `R′ < 0` there instead. In the middle, ball arithmetic encloses `R` on 3219 intervals (`r = 5`). A heuristic from the functional equation explains the threshold: once the arc reaches height `2π` while moving right through `Re z < 0`, `|ζ|` falls.

Preprint v1, 12 October 2026, not peer reviewed. Computer assisted: every number is a ball enclosure (Arb, through python-flint 0.9.0). The exact reductions are formally verified in Lean 4 (`lean/`, standard axioms only): the identity `Re(z′/(z − z₀)) = ½ cot(u/2)`, the splitting of `ζ′/ζ`, the bound used near the start, `R(π) = 0`, and the step from `R′ < 0` to `R > 0`. The enclosures themselves are outside Lean. The author used AI tools (Claude, Anthropic), as stated in the paper, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`; `figs/arcs.tex` is written by `verify/fig_arcs.py`.
- `verify/`:
  - `prove.py`: the case `r = 5` asked in the question; prints `PROVED`. `MUTANT=1` (claim monotonicity past `π`) must print `NOT PROVED`.
  - `semicircles.py`: both theorems. `MUTANT=1` (claim monotonicity for `r = 7`) and `MUTANT=2` (look for a decrease for `r = 3`) must print `NOT PROVED`.
  - `fig_arcs.py`: the figure (mpmath, plotting only).
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 prove.py && MUTANT=1 python3 prove.py | tail -1
python3 semicircles.py && MUTANT=1 python3 semicircles.py | tail -1; MUTANT=2 python3 semicircles.py | tail -1
python3 fig_arcs.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

`prove.py` and `semicircles.py` need `python-flint`; `fig_arcs.py` needs `mpmath`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
