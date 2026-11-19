# Positivity of an alternating sum from random overlaps in C^N

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/alternating-sum.svg" width="760" alt="An alternating sum that is never negative"></p>

<p align="center"><b>Abdesselam's sum L(u,a,b,n) is nonnegative, and Taylor's and Hucht's conjectures follow.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Abdesselam asked on MathOverflow (question 498232) whether a certain triple sum of factorials with alternating signs, `L(u,a,b,n)`, is always nonnegative. The sums are the coefficients of a joint moment of overlaps of random unit vectors in `C^N`, expanded in rising factorials of `N - 1`, so their positivity says that the moment is a nonnegative combination of those rising factorials. (That the moment itself is nonnegative for real `N ≥ 1` already follows from the law of the overlaps: Beta(1, N − 1) for whole N ≥ 2 and the constant 1 for N = 1, and for every real N > 1 the same expectation over independent Beta(1, N − 1) variables agrees with the rational function at every whole N; the content is the sign of each coefficient.)

The answer is yes. `L` is a positive factorial multiple of the coefficient of `w^a z^b` in `R^(u+1) (R-1)^ν`, where `R = 1/((1-z)^2 - w^2)` and `ν = a + b - n` (Theorem 1), and every coefficient of that series is nonnegative. The same formula gives `L > 0` exactly when `a` is even and `n ≥ a/2`, proves Peter Taylor's conjectures from the MathOverflow thread (`ν! L/(u+ν)!²` is a polynomial in `u` with nonnegative coefficients, of degree `n - a/2` for even `a` and `n ≥ a/2`, given by his binomial-basis formula; the case `u = 0` of that formula was proved earlier by Hjalmar Rosengren in [MathOverflow 499242](https://mathoverflow.net/q/499242), where Max Alekseyev proved its vanishing for `n < a/2`; since the expansion reduces every `u` to `u = 0`, Rosengren's identity already implies Taylor's formula, and what is new here is the generating function, the nonnegativity and the degree), shows that Fred Hucht's terminating ₃F₂ series are positive for `μ + ν ≤ c` (his guess for `μ + ν > c` is not covered), and recovers Abdesselam's evaluation of the extreme case `n = a + b`. The result concerns the two-site case; it does not settle the open problems on general graphs in Abdesselam's arXiv:2207.07603.

Preprint v3, 19 November 2026 (v1: 8 October 2026), not peer reviewed. Zenodo: [doi:10.5281/zenodo.24372452](https://doi.org/10.5281/zenodo.24372452), identical to this folder at tag `alternating-sum-positivity-v3`. Version 3, after a referee review by Codex (OpenAI), states that Rosengren's identity with the reduction in `u` already gives Taylor's formula, fixes the `N = 1` case of the Beta law and the description of Hucht's antisymmetry, adds direct checks of Taylor's complete formula, and moves the Lean mutants to a harness that treats timeouts and crashes as failures; the theorems are unchanged. Version 2 corrects the motivation and the abstract and credits Rosengren and Alekseyev; the theorems, the verification program and the Lean are unchanged. Every result of the paper is formally verified in Lean 4 (`lean/`, standard axioms only); Abdesselam's identity relating the moment to the numbers `L` is taken from the question. The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `AlternatingSum/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `scripts/mutants.toml`, run by `scripts/mutate.py`, plants seventeen wrong changes and checks that Lean rejects each one with an error in the mutated copy.
- `verify/verify_paper.py`: checks in exact arithmetic, against the triple sum as defined in the question, Theorem 1, every corollary, the coefficients of `R^(u+1)`, Taylor's complete formula, its reduction to `u = 0` and its degree, and the example values; Taylor's inner sums and Hucht's ₃F₂ form against the coefficients of `R (R−1)^k`, with the positivity of Hucht's series; and identity (2) as rational functions of `N`. Seven planted mutants are killed; `ALL CHECKS PASSED` prints only after every check and mutant.

## Reproduce

```
cd verify
python3 verify_paper.py                 # needs sympy; about three minutes on an Apple M-series laptop
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
python3 -I scripts/mutate.py scripts/mutants.toml   # seventeen mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
