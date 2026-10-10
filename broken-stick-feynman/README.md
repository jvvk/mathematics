# A broken stick and a Feynman diagram

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a56f33dfb3cc4e4d00cef571d0339b3cdb9f0ce3/assets/broken-stick.svg" width="760" alt="A broken stick and a Feynman diagram"></p>

<p align="center"><b>The chance that six random pieces of a stick make a tetrahedron is a three-loop Feynman diagram; it is 0.0125749944…, not 1/79.</b><br><sub>Partial progress · algebra formally verified in Lean · no closed form</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Break a stick at five random points and lay the six pieces, in a fixed order, on the edges of a tetrahedron. Benjamin Dickman asked on MathOverflow ([question 142983](https://mathoverflow.net/q/142983)) how often a tetrahedron with these edge lengths exists. No exact value is known, and the numbers so far were numerical estimates, one of which, `1/79`, turns out to be wrong.

The note shows that the probability is a Feynman integral. For `N = n(n+1)/2` pieces laid on the edges of an `n`-simplex,

`p_n = C_n ∫ ∏ β_e^((n−2)/2) e^(−Σβ) / U(β)^((n+1)/2) dβ`,   `C_n = 2^(N−n) π^(−N/2) Γ_n((n+1)/2)`,

where `U` is the first Symanzik polynomial of the complete graph `K_{n+1}` (a sum over spanning trees). So `p_n` is the vacuum diagram of `K_{n+1}` in dimension `n + 1` with unit masses and every propagator raised to the power `n/2`:

- `n = 2`: a one-loop triangle in three dimensions, which gives the classical `1/4`;
- `n = 3`: the three-loop tetrahedron in four dimensions with propagators `(q² + 1)^(−3/2)`, `p_3 = (π²/16) T`;
- `n = 4`: `p_4 = 1.0584 × 10^(−4)` (Monte Carlo).

The route is classical step by step (exponential spacings, Schoenberg's criterion, the Schwinger representation, Siegel's matrix gamma integral, Kirchhoff's matrix-tree theorem); the identity itself is new as far as a dated literature search could find. Two independent computations give `p_3 = 0.0125749944167…`, agreeing to within `10^(−12)`, which corrects the value `1/79` reported from simulation. For the question as asked, with the pieces placed in any order, the probability is `0.0652818 ± 0.0000004`, consistent with an earlier estimate. No closed form is known.

Preprint v1, 10 October 2026, not peer reviewed and not yet independently reviewed. The algebra of Theorem 1 for the triangle and the tetrahedron is formally verified in Lean 4 (`lean/`, standard axioms only); the analytic inputs are quoted. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex`, `note.pdf` and the figure sources `fig_*.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs 14 mutation tests.
- `verify/`:
  - `marked.py`: `p_3` by the hinge reduction and quadrature in elliptic coordinates (`cyl` mode), the triangle control, and plain Monte Carlo.
  - `feynman_hp.py`: `p_3` from the simplex form of Theorem 1 by sector decomposition and Gauss quadrature; `feynman.py` the same by Monte Carlo.
  - `general_n.py`: Theorem 1 tested by Monte Carlo on both sides for `n = 2, 3, 4` (`general_n.log` is the run quoted in the paper).
  - `unmarked.c`: the unordered probability by randomised quasi-Monte Carlo over the 30 essentially different orders.
  - `check.py` asserts every number stated in the paper; `mutants.py` checks that six wrong variants of the programs fail it.
  - `recheck/recheck.py`: an independent check sharing no code with the rest (direct Monte Carlo excluding `1/79`, the simplex form with its own spanning-tree enumeration, the constants in mpmath, Zare's `1/54`, `p_4`, the unordered value over all 720 orders) and three mutants of its own. `recheck-full.log` is the full run.

## Reproduce

```
cd verify
python3 check.py && python3 mutants.py            # about a minute each
python3 marked.py cyl 40 20                         # p_3 = 0.0125749944167..., about 30 s
python3 feynman_hp.py 44                            # the second method, about a minute
python3 general_n.py 2e7                            # Theorem 1 for n = 2, 3, 4
cc -O2 -o unmarked unmarked.c -lm && ./unmarked unmarked 26 16 1   # unordered probability
python3 recheck/recheck.py                          # about two minutes
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

The Python programs need NumPy, SciPy and mpmath.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
