# Four acute faces

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/89386c689c9708dfb532b374de072944fa86006b/assets/four-acute-faces.svg" width="760" alt="Four acute faces"></p>

<p align="center"><b>Four random points on a sphere span a tetrahedron with four acute faces with probability exactly 1/12: flipping signs gives eight tetrahedra, and on average 2/3 of them succeed.</b><br><sub>Answers a question · in Lean, including the probability</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Choose four points independently and uniformly on the unit sphere in `ℝ³`. What is the probability that all four faces of the tetrahedron they span are acute triangles? MathOverflow [question 498296](https://mathoverflow.net/q/498296) (also Mathematics Stack Exchange [5083355](https://math.stackexchange.com/q/5083355)) asked whether it is `1/12`. Simulations suggested so, and for a single face the probability is `1/2`, so the faces are far from independent.

**Theorem.** The probability is exactly `1/12`.

The proof flips signs. Replacing some of the four points by their antipodes gives eight tetrahedra, and the expected number of them with four acute faces is `8 · (1/12) = 2/3`. An angle is obtuse exactly when a signed sum of three of the unit vectors is short (length below `1`). A finite count shows that the number `N` of good tetrahedra among the eight satisfies `N + C = 4`, where `C` counts tetrahedra with one or two short face sums. So `E N` reduces to two pair integrals on the sphere, `1/6` and `1/24`, which follow from Archimedes' theorem that the height of a uniform point on the sphere is uniform.

The same proof, in a different form, had already appeared in a ChatGPT conversation shared by Timothy Chow and linked from a MathOverflow comment on 14 August 2026. The paper credits it, and its contribution is expository: a complete, checked and formalised account. The author's MathOverflow answer ([515661](https://mathoverflow.net/a/515661), 1 October 2026) was found with Claude (Anthropic) without the author having read that conversation.

Preprint v1, October 2026, not peer reviewed; submitted to arXiv. The whole theorem, including the probability measure, Archimedes' theorem and the two integrals, is formally verified in Lean 4 (`lean/`, standard axioms only). Only the closing remarks of the paper are outside Lean. The author used AI tools (Claude, Anthropic) in this work, as stated in the paper, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf` (the arXiv version), with `figs/`.
- `verify/`:
  - `check_identities.py`: exact rational checks of every finite step. It covers the angle identity, the threshold, the face and angle correspondence, `N + C = 4` on 400 exact configurations, all corner shapes, all 65,536 sign subsets, the worked example and the final arithmetic. `MUTANT=1` (a wrong threshold for short sums) and `MUTANT=2` (a wrong value for `∫ √u`) must fail.
  - `sim_N.py`: Monte Carlo with 400,000 samples of the number of good tetrahedra among the eight. The mean is about `0.667`, giving about `0.0834` for the probability.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check_identities.py && MUTANT=1 python3 check_identities.py; MUTANT=2 python3 check_identities.py
python3 sim_N.py
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
