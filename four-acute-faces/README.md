# Four acute faces

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/89386c689c9708dfb532b374de072944fa86006b/assets/four-acute-faces.svg" width="760" alt="Four acute faces"></p>

<p align="center"><b>Four random points on a sphere span a tetrahedron with four acute faces with probability exactly 1/12: flipping signs gives eight tetrahedra, and on average 2/3 of them succeed.</b><br><sub>Answers a question · in Lean, including the probability</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Choose four points independently and uniformly on the unit sphere in `ℝ³`. What is the probability that all four faces of the tetrahedron they span are acute triangles? MathOverflow [question 498296](https://mathoverflow.net/q/498296) (also Mathematics Stack Exchange [5083355](https://math.stackexchange.com/q/5083355)) asked whether it is `1/12`. A single face is acute with probability `1/2`, but the faces share edges, so they are far from independent.

**Theorem.** The probability is exactly `1/12`.

An angle of a triangle on the sphere is obtuse exactly when a signed sum of its three vertices is short (length below `1`). Replacing points by their antipodes gives eight tetrahedra, and an obtuse angle of one of them is a short face sum of another. Every even tetrahedron shares exactly one face with every odd one, so the sixteen triangles fill a `4 × 4` grid, and a tetrahedron has four acute faces exactly when every short cell lies in its row or column. A threshold on the tetrahedra's totals makes the short cells a small staircase, and the six possible staircases give `N = 4 − 2m + J` for the number `N` of good tetrahedra, where `m` counts short cells and `J` pairs of short cells in one line. Archimedes' hat-box theorem gives the two probabilities needed, `1/6` and `1/24`, so `E N = 2/3` and the answer is `2/3 ÷ 8 = 1/12`.

The theorem and the method first appeared in a ChatGPT conversation publicly shared by Timothy Chow and linked from a MathOverflow comment on 14 August 2026. The paper credits it and claims no priority. Its contribution is the exposition. The author's MathOverflow answer ([515661](https://mathoverflow.net/a/515661), 1 October 2026) was found with Claude (Anthropic) without the author having read that conversation.

Preprint v2, October 2026, not peer reviewed. Version 1 (tag `four-acute-faces-v1`) was prepared with Claude (Anthropic) and OpenAI Codex; this version replaces it. The paper's declaration: the exposition is the author's own; Claude Opus 5.5 (Anthropic) was used to help draft the paper. Separately from the paper, a Lean 4 formalisation of the full theorem, including the probability measure, Archimedes' theorem and both integrals, is in `lean/` (standard axioms only); it was written with Claude Opus 5.5.

**Version 3** (23 October 2026, tag `four-acute-faces-v3`): expository revision of the paper (the grid of Section 3 worked out for the paper's rational example (new Figure 2), and one phrase of the abstract). The results, programs and Lean files are unchanged from v2.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`. Figures are drawn in TikZ inside the source.
- `verify/`:
  - `check.py`: exact rational checks of every finite claim on 600 configurations of rational points on the sphere: the grid, the acute-face criterion (with `N` counted directly from the angles), the threshold, the staircase, the three restrictions, `N = 4 − 2m + J`, the worked example and the final arithmetic. `MUTANT=1` (threshold `3`) and `MUTANT=2` (`N = 4 − 2m + 2J`) must fail.
  - `sim.py`: Monte Carlo estimate from one million random tetrahedra, about `0.0838`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps the paper to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check.py && MUTANT=1 python3 check.py; MUTANT=2 python3 check.py
python3 sim.py
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
