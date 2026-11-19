# Three tangent circles and a fair coin

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/tangent-circles.svg" width="760" alt="Three circles and a fair coin"></p>

<p align="center"><b>A triangle through random points on three touching circles contains the incentre with probability exactly 1/2, for all radii.</b><br><sub>Open problem settled · verified by computation · partly in lean; geometry by hand</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Three circles of positive radii touch externally in pairs, and a triangle is formed by choosing one uniform random point on each. Dan asked on Mathematics Stack Exchange and MathOverflow ([question 498968](https://mathoverflow.net/q/498968)) why the triangle contains the incentre of the triangle of centres with probability `1/2`; the equal-radius case had been done by an integral, and for unequal radii Dan had reduced the question to a statement about two circles that he checked numerically.

The probability is `1/2` for all radii (Theorem 1). The key is a fact about two touching circles: a random chord joining them crosses the common tangent at a point from which the two centres are seen at an angle uniformly distributed on `(π/2, π)` (Theorem 2). Each side of the triangle then misses the incentre with probability equal to the opposite angle of the triangle of centres divided by `2π`, and these angles sum to `π`. That last step is Dan's reduction ([MSE answer 5087836](https://math.stackexchange.com/a/5087836), 4 August 2025), conditional on the two-circle law, which he had checked numerically and asked about separately; the new part here is the proof of that law (Theorem 2), whose coordinates (crossing height and direction) Maxicl suggested in comments on the question. A refinement maps the pair of random points to a uniform point on a sphere, on which each miss is a lune (Theorem 3). The proof of Theorem 2 is a computation; the intuitive proof that the question asked for remains open.

Preprint v2, 19 November 2026 (v1: 9 October 2026), not peer reviewed. **Version 2**, after a referee review by Codex (OpenAI): credits Dan's reduction and Maxicl's coordinates, requires external tangency and positive radii, states the signed angles exactly, sets aside the probability-zero configurations, and narrows the Lean claim; the checking scripts now exit nonzero on failure and skip mutant cases that coincide with the claim. Selected identities and integrals used in the proofs are formally verified in Lean 4 (`lean/`, standard axioms only): the chord identities, the integral equal to `π`, the density and its distribution function, the half-angle identity, the final sum and the sphere's folding step. The probability laws themselves, the sphere map as a statement about measures, the change of variables and the plane geometry of Lemmas 1 and 2 are checked by hand and by simulation, not in Lean. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.toml`, run by `scripts/mutate.py`, holds the mutation tests.
- `verify/`:
  - `recheck/recheck.py`: an independent check from the definitions: `P = 1/2` for four radius triples by a barycentric test, the per-side miss probabilities, disjointness, the inner-arc probabilities, the uniform angle (Kolmogorov-Smirnov), the joint law of the sphere coordinates, the integral by quadrature, and three mutants. `--quick` for a short run; `recheck/recheck-full.log` is the output of the full run (command, date and versions in its first line).
  - `verify.py`, `verify_steps.py`, `verify_sphere_map.py`: the earlier step-by-step checks of the crossing lemma, each intermediate identity, and the eight-sheet sphere map (inverse Jacobians, round trips), each with mutants. Simulation and quadrature, not proofs.

## Reproduce

```
cd verify
python3 recheck/recheck.py --quick
python3 verify_steps.py && python3 verify_sphere_map.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

Python needs `numpy` and `scipy`.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
