# Does the smallest enclosing copy fit? Random points in a convex polygon

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/enclosing.svg" width="760" alt="Does the smallest copy fit?"></p>

<p align="center"><b>For many random points in an equilateral triangle, the smallest enclosing copy fits inside with probability tending to 13/48, not 1/2.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Drop `n` random points into a disk and draw the smallest circle containing them: does it lie inside the disk? An answer on Mathematics Stack Exchange shows that the limiting probability is 1/2 ([question 4799757](https://math.stackexchange.com/q/4799757)). A follow-up on MathOverflow asked whether the same holds for a regular polygon and a smallest enclosing regular polygon, which may be rotated ([question 458571](https://mathoverflow.net/q/458571)).

The answer is no. For `n` uniform points in a convex polygon `K`, the probability that some smallest similar copy of `K` containing them lies inside `K` converges to an explicit constant `p(K)`, given by a formula over a Poisson limit model (Theorems 1 and 10). For triangles the formula is explicit (Corollary 2): `p = 13/48` for the equilateral triangle, `7/24` for the right isosceles triangle, `29/96` for the 30-60-90 triangle. For the regular `q`-gon (Corollary 3),

`p_q = q tan(π/q) E[Vol(T) 1{0 ∈ int T}] + 1{q even} 8/(3q²)`,

where `T` is the tetrahedron spanned by four independent points, each on a uniformly chosen vertical edge of the prism `P_q × [-1, 1]` at a uniform height; `p_4 = 1/4`, and numerically `p_q` settles near 0.146, far from the disk's 1/2. The reason is the freedom to rotate the enclosing copy, which the disk does not have.

Preprint v1, 8 October 2026, not peer reviewed. Every theorem, lemma and corollary is formally verified in Lean 4 (`lean/`, standard axioms only); the exposition has not yet been independently reviewed. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `enclosing.tex`, `enclosing.pdf` and the figure source `fig_example.tex`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, about 20,500 lines. `EnclosingCopy/Poisson` builds finite Poisson point processes, the multivariate Mecke equation and the comparison of iid samples with Poisson processes on shrinking windows (Mathlib has no point processes); `EnclosingCopy/Enclosing` formalises the paper. `lean/README.md` maps each result of the paper to its Lean name, and `Enclosing/Main.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `lean/scripts/` holds the mutation tests: each plants a wrong constant, hypothesis or inequality in one file and checks that it no longer compiles.
- `verify/`: the programs behind the numerical statements of Section 8.
  - Limit model by Monte Carlo: `general_K.py` (any polygon), `limit_fast.py` (triangle and square).
  - Formulas evaluated: `triangle_exact.py`, `triangle_closed.py` (Corollary 2, and the scan of 28,800 triangle shapes), `formula_K.py`, `formula_par.py` (Theorem 10 for polygons without and with parallel sides), `general_p.py`, `prism.py` (odd `q`) and `even_p.py` (Corollary 3).
  - Finite problem, exact geometry: `direct.py` (Table 3; its outputs are in `results/direct_results.txt`), `finite_K.py`, `sim.py`.
  - `recheck/triangle_values.py`: the triangle values of Corollary 2 from the closed form found in the formalisation, sharing no code with the programs above.

The numerical values (Tables 1 to 3, the triangle-shape scan, `p_q` for `q ≥ 5`) and Conjecture 4 are not formally verified.

## Reproduce

```
cd verify
python3 recheck/triangle_values.py                 # Corollary 2 values, seconds
python3 triangle_closed.py                         # Corollary 2 against triangle_exact.py, then the shape scan
python3 even_p.py 6 20000000 1                     # p_6, Table 1 (even q)
python3 general_p.py 5 20000000 1                  # p_5, Table 1 (odd q); prism.py 5 ... is the second implementation
python3 formula_par.py hexagon 2000000 1           # Table 2, formula column
python3 general_K.py hex_cs_irreg 20000 1          # Table 2, limit-LP column
python3 direct.py 3 1000 100000 1                  # Table 3, one row
cd ../paper && latexmk -pdf enclosing.tex
cd ../lean && lake exe cache get && lake build     # builds every module and prints the axiom audit
```

The scripts take NumPy and SciPy. Set `TIME_LIMIT=<seconds>` to cap a long run: the simulation scripts (`direct.py`, `general_K.py`, `limit_fast.py`, `sim.py`, `finite_K.py`, `general_p.py`) then print the estimate from the trials completed; the others stop. The Lean build takes about an hour on a laptop after the Mathlib cache is fetched.

## Licence

The paper and figure are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
