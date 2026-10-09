# Descent sets of a permutation and its inverse: almost every pair occurs

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/descent-sets.svg" width="760" alt="Descent sets of a permutation and its inverse"></p>

<p align="center"><b>Almost every pair of subsets occurs, so Stanley's growth rate is L = 4.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Richard Stanley asked how many pairs (S, T) of subsets of {1, …, n−1} arise as the descent sets of a permutation w of {1, …, n} and of its inverse, and what the growth rate L = lim f(n)^(1/n) is. The paper proves that almost every pair arises, 1 − f(n)/4^(n−1) ≤ 6e^(−n/150) for every n, so L = 4. An elementary obstruction (if T contains |S| + 1 consecutive integers, the pair cannot occur) gives f(n) ≤ 4^(n−1) − 3^(n−1) + 1, so the rate cannot exceed log(4/3). The pairs violating a necessary condition of Gale–Ryser type have proportion (3/4)^(n+O(log² n)), so the rate is exactly log(4/3) if a dominance-order criterion for occurrence, checked by computation for n ≤ 20, is correct. It also finds the asymptotics of the number of permutations w such that w and w⁻¹ are both alternating, g(n) = (16/π²)(4/π²)^n n! (1 + π⁴/(48n) + O(n⁻²)), confirming Stanley's prediction, and checks Gessel's conjecture on the largest class for n ≤ 22.

The question is Stanley's ([MathOverflow question 486548](https://mathoverflow.net/q/486548)). The proof that L = 4 was first posted as the author's [MathOverflow answer](https://mathoverflow.net/a/515793) on 7 October 2026.

Preprint, 8 October 2026.

**Status.** All proved results are formally verified in Lean 4 and all computations were independently rechecked; the proofs have not yet been checked line by line by a human.
**Origin.** The results and proofs were found with the AI systems Claude (Anthropic) and Codex (OpenAI), directed by the author.

## Contents

- `paper/`: `paper.tex` and `paper.pdf` (Electronic Journal of Combinatorics format, `e-jc.sty`), the figure source `figs/rowwords.tex`, and `abstract.txt`.
- `lean/`: its own Lake project, pinned to Lean 4.34.0 and the Mathlib revision in `lake-manifest.json`. It proves Theorem 1.1 (`Stanley.DensitySharp.density_ratio`), L = 4 (`Stanley.tendsto_f`), Lemma 2.1 in both directions without the insertion algorithm (`Stanley.Growth.mem_pairs_iff_words`, via Fomin's growth diagrams), the bound of Remark 3.4 (`Stanley.f_add_three_pow_le`), Theorem 1.2 from the definition of g(n), including Stanley's generating function and the Euler-number series (`Stanley.Alt.g_asymptotics`), the diagonal reduction of Remark 4.1, the necessary direction of Conjecture 5.1 (Lemma 3.5), Theorem 3.6 (`Stanley.Alt.gr_rate`, with the (3/4)^(n+O(log² n)) form as `Stanley.Alt.gr_rate_asymp`) and Corollary 3.7 (`Stanley.Alt.cor_rate`). `CheckClaims.lean` prints each statement and its axioms (only `propext`, `Classical.choice`, `Quot.sound`); `axiom-validation.txt` is its saved output. `scripts/mutants.sh` checks that deliberately wrong variants fail to compile. `LeanProofs/Vendor/OAI` is McDiarmid's inequality, vendored from [openai/math](https://github.com/openai/math) under the Apache License 2.0.
- `verify/`: the computations behind every number in the paper, with saved outputs in `verify/results`. `computations/independent/` holds programs that share no code with the others: a dynamic programme on Young's lattice that checks the dominance-interval criterion for every pair with n ≤ 20 and Gessel's conjecture for n ≤ 22, a from-scratch recheck of every other stated number, and a separate check of the failure probabilities in Remark 3.4.

## Reproduce

```
cd lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
cd ../verify/computations/independent && python3 recheck.py ../../../paper/figs/rowwords.tex
clang++ -O3 -std=c++17 search.cpp -o search && ./search 13
cc -O3 gr_check.c -o gr_check -lm && ./gr_check 24
cd ../../../paper && latexmk -pdf paper.tex
```

The other scripts in `verify/computations` and their commands are described in `verify/README.md`.

## Licence

The paper and figures are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE). The vendored files in `lean/LeanProofs/Vendor/OAI` remain under the Apache License 2.0.
