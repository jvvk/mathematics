# Why the sphere beats the ball

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/b6f7c35559d237196e60afc0b8d4d56609168bd4/assets/sphere-ball.svg" width="760" alt="Why the sphere beats the ball"></p>

<p align="center"><b>Three points on concentric spheres form an acute triangle with probability at most 1/2, equal only when the two outer radii agree; so the uniform sphere beats every rotationally invariant law in space, while in the plane moving mass inwards helps.</b><br><sub>Partial progress · formula and bound formally verified in Lean · the disc's gain unexplained</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Three random points form an acute triangle with probability `1/4` on a circle, `4/π² − 1/8 ≈ 0.280` in the disc, `1/2` on a sphere and `33/70 ≈ 0.471` in the ball (Hall, 1982). Filling in the circle helps, filling in the sphere hurts. Dan asked on MathOverflow ([question 484567](https://mathoverflow.net/q/484567)) why.

**Theorem.** Let `A, B, C` be independent and uniform on concentric spheres in `ℝ³` of radii `a ≥ b ≥ c > 0`, and `h = √max(0, b² + c² − a²)`. Then

`P(ABC acute) = b/(2a) + c²/(6ab) − h³/(6abc) ≤ 1/2`,

with equality exactly when `a = b`.

**Corollary.** For independent points with any common rotationally invariant distribution on `ℝ³`, the probability of an acute triangle is at most `1/2`, with equality only for the uniform distribution on a sphere. So the ball must lose to the sphere, whatever its exact value; this settles the rotationally invariant case of [MSE 5012846](https://math.stackexchange.com/q/5012846), whose general case is open.

The proof uses Archimedes' hat-box theorem: with two vertices fixed, the third gives an obtuse angle exactly when it lies in a cap of its sphere, and the cap's share is a clipped uniform tail. Each of the three obtuse probabilities is then the integral of a polynomial, and the bound is a one-variable monotonicity argument with `b²c² − a²h² = (a² − b²)(a² − c²)`. In the plane the picture differs: a vertex at the centre gives an acute triangle half the time in either dimension, better than the circle's `1/4` but no better than the sphere's `1/2`, so a little mass at the centre helps the circle and hurts the sphere. A direct reason for the uniform disc's gain is still missing.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The three cap integrals, the formula, the bound with its equality case and the plane/space comparison are formally verified in Lean 4 (`lean/`, standard axioms only); the hat-box theorem and the conditioning are quoted. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf` and the figure sources `fig_*.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names and lists what is quoted, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 10 mutation tests.
- `verify/`:
  - `verify.py`: 879 assertions: the three cap probabilities against direct numerical integration of the defining integrals for 43 radius triples, exact radial identities, the mixtures and the ball arithmetic; `run_checks.py` runs it and six deliberate mutations, all rejected.
  - `recheck/recheck.py`: an independent check sharing no code with `verify.py`: simulation of actual points for seven radius triples, the ball and both mixtures, and exact symbolic integration of the formula to `33/70`; three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 run_checks.py         # a few seconds; needs SciPy and SymPy
python3 recheck/recheck.py    # about ten seconds; needs NumPy and SymPy
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
