# A determinant dichotomy for quadratic zero-one systems

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/2c8c0a471a4eca97ef8c252419e874f69e25e3cf/assets/steady-states.svg" width="760" alt="A determinant dichotomy for quadratic zero-one systems"></p>

<p align="center"><b>For three-species quadratic zero-one networks, one 3 × 3 determinant of quadratic rate constants decides the global dynamics: negative means an absorbing box and an odd number of steady states, positive means finite-time escape and an even number. Four and five steady states are attained, with seven and eight reactions.</b><br><sub>Partial answer to Tang and Zhang's question · both extreme examples in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Tang and Zhang ([arXiv:2608.01116](https://arxiv.org/abs/2608.01116)) proved by computer classification that a three-species quadratic zero-one reaction network with six reactions has at most three nondegenerate positive steady states, and asked why; Bernstein's theorem allows five. This paper studies the sign class behind their question: three-variable quadratic systems in which a monomial's coefficient in the `i`-th equation is negative exactly when the monomial contains `x_i`.

- **Theorem 2.1 (the dichotomy).** For systems with all 21 admissible coefficients nonzero, let `B` be the 3 × 3 matrix of quadratic coefficients and `Δ = det B ≠ 0`. If `Δ < 0`, every positive solution is global, a box absorbs every trajectory, the Brouwer degree is `−1`, and a regular system has 1, 3 or 5 positive steady states. If `Δ > 0`, an open set of initial conditions escapes in finite time, the degree is `0`, and the count is 0, 2 or 4.
- **Corollary 2.2.** The bound four in the escape region holds for sparse systems too, and it is sharp.
- **Section 5.** An elementary seven-reaction network with integer rates has exactly four positive steady states, two of them stable, coexisting with an explicit finite-time escape region.
- **Theorem 6.1.** An eight-reaction network has exactly five positive steady states (the Bernstein bound), three of them stable; its determinant is negative, as the dichotomy requires.

Odd parity in the dissipative case is already part of the degree framework of Conradi, Feliu, Mincheva and Wiuf, and the vertex technique is due to Belta–Habets and Ben Sassi–Girard; the paper's contribution is the coefficient-level combination for this sign class, the sharp bound, the link to finite-time escape, and the two extreme examples. Whether five steady states need eight reactions or already occur with seven is open.

Preprint v1, 20 October 2026, not peer reviewed. Both extreme examples (exact steady-state sets, root intervals and Jacobian signs) are formally verified in Lean 4 (`lean/`, standard axioms only); the dichotomy itself is proved by hand from standard degree theory, and stability counts are exact Routh–Hurwitz certificates. Two AI tools were used in this work under the author's direction (OpenAI Codex and Claude, Anthropic), as described in the paper's acknowledgements, and the author is responsible for its content.

## Contents

- `paper/`: `steady-state-dichotomy.tex` and `steady-state-dichotomy.pdf`.
- `verify/` (Python 3 with SymPy):
  - `recheck_paper.py`: an independent recheck of every finite claim in the paper from the reaction lists (37 checks: the mass-action systems, eliminants, root counts, determinant signs, the escape region and its time bound, the five-state network, Routh–Hurwitz stability counts). Shares no code with the verifier. About 1 second.
  - `verify_dichotomy.py`, `certify_exact.py`: the exact verifier. For strict examples with `N = 0, …, 4` positive states (`strict_*.json`) it rebuilds the exact root certificates (`certificate_*.json`) and checks the determinant signs, degree sums and the inward or outward barrier inequalities; `dichotomy_evidence.json` is its output. About 1 second.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the 21 mutation tests.

## Reproduce

```
cd verify && python3 recheck_paper.py | tail -1 && python3 verify_dichotomy.py | tail -1
cd ../paper && latexmk -pdf steady-state-dichotomy.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
