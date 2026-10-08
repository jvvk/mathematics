# Positivity of an alternating sum from random overlaps in C^N

Abdesselam asked on MathOverflow (question 498232) whether a certain triple sum of factorials with alternating signs, `L(u,a,b,n)`, is always nonnegative. The sums are the coefficients of a joint moment of overlaps of random unit vectors in `C^N`, expanded in rising factorials of `N - 1`, so their positivity makes that moment nonnegative for every real `N ≥ 1`, not only for whole numbers.

The answer is yes. `L` is a positive factorial multiple of the coefficient of `w^a z^b` in `R^(u+1) (R-1)^ν`, where `R = 1/((1-z)^2 - w^2)` and `ν = a + b - n` (Theorem 1), and every coefficient of that series is nonnegative. The same formula gives `L > 0` exactly when `a` is even and `n ≥ a/2`, proves Peter Taylor's conjectures from the MathOverflow thread (`L` is a polynomial in `u` with nonnegative coefficients, of degree `n - a/2`, given by his binomial-basis formula), shows that Fred Hucht's terminating ₃F₂ series are positive in the range where they appear (`μ + ν ≤ c`), and recovers Abdesselam's evaluation of the extreme case `n = a + b`. The result concerns the two-site case; it does not settle the open problems on general graphs in Abdesselam's arXiv:2207.07603.

Preprint v1, 8 October 2026, not peer reviewed. Every result of the paper is formally verified in Lean 4 (`lean/`, standard axioms only); Abdesselam's identity relating the moment to the numbers `L` is taken from the question. The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `AlternatingSum/Audit.lean` prints the axioms of every one. `SOURCE-SNAPSHOT.json` records the development commit and the hash of every file. `mutants.sh` plants seventeen wrong changes and checks that each fails to compile.
- `verify/verify_paper.py`: checks in exact arithmetic, against the triple sum as defined in the question, Theorem 1, every corollary, the coefficients of `R^(u+1)`, Taylor's formula and degree, Hucht's identity and positivity, the example values and identity (2) as rational functions of `N`; five planted mutants are killed.

## Reproduce

```
cd verify
python3 verify_paper.py                 # needs sympy; under a minute
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build   # builds every module and prints the axiom audit
./mutants.sh                                     # seventeen mutants, each rejected
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
