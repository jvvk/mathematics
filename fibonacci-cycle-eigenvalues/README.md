# Double eigenvalues of cycles weighted by the Fibonacci word

<!-- visual:start -->
<p align="center"><b>Weight the edges of an n-cycle 1 or 2 along the Fibonacci word. At n = 4F<sub>k</sub> (k ≥ 4) exactly F<sub>k</sub> eigenvalues of the Laplacian are double, and at the eigenvalue 1 the only other doubles are at n = 33, 53, 106.</b><br><sub>Conjecture settled (main part) · certified computation, no Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Give the edges `{i, i+1}` of the `n`-cycle the weight `a` or `b` according as letter `i` of the Fibonacci word `ABAABABAAB…` is `A` or `B`. Scott M. Foltz ([OEIS A401899](https://oeis.org/A401899), 15 November 2026, weights 1 and 2) conjectured that the Laplacian has `3F_k` distinct eigenvalues when `n = 4F_k`, and that otherwise all `n` are distinct except on a sparse set with one double eigenvalue.

- **Theorem 1.1.** For `k ≥ 4` and all positive weights `a ≠ b`, the `4F_k`-cycle has exactly `F_k` double eigenvalues, the spectrum of the `F_k`-cycle twisted by the phase `i`, and every other eigenvalue is simple. So `a(4F_k) = 3F_k`.
- **Theorem 1.2.** For weights 1 and 2, the number 1 is a double eigenvalue of the `n`-cycle exactly when `n ∈ {20, 33, 53, 106}`. The proof is 2-adic.
- **Proposition 4.4.** For `a, b > 0`, `a ≠ b` and `k ≥ 4`, the `F_k`- and `2F_k`-cycles have only simple eigenvalues.
- **Conjecture 6.1.** For weights 1 and 2 the only double eigenvalues off `n = 4F_k` are those of Theorem 1.2. Exact search: none other for `n ≤ 6000`; none at all off `n = 4F_k` for four other weight ratios, `n ≤ 2000`.

Preprint v1, 21 November 2026, not peer reviewed; this version predates the author's line-by-line read. Zenodo: [doi:10.5281/zenodo.24419102](https://doi.org/10.5281/zenodo.24419102), identical to this folder at tag `fibonacci-cycle-eigenvalues-v1`. The proofs, programs and text were produced with Claude Opus 5.5 (Anthropic) under the author's direction, and OpenAI Codex refereed the argument and the programs, as described in the paper's acknowledgements; the author is responsible for the content.

## Contents

- `paper/`: `fibonacci-cycle.tex`, `fibonacci-cycle.pdf`.
- `verify/` (Python 3 with numpy, sympy, python-flint; run from `verify/`). Every script except `spec.py` (helpers) asserts its results and exits nonzero on failure.
  - `certify.py K a b`: Theorem 1.1 exactly for `k = 4..K`: the gcd of the entries of `M − I` over `Q[λ]` has degree `F_k` and divides the squarefree `tr M_U`.
  - `scan.py N a b`: exact scan of all `n ≤ N`: the `4F_k` counts, squarefree gcds, and, for the five tabulated ratios `b/a` only, the exceptional set (`{33, 53, 106}` for `b/a = 2`, empty for `7/15, 3, 5/2, 4`), asserted up to `n ≤ 6000` (`b/a = 2`) and `n ≤ 2000` (others); beyond those ranges, and for other ratios, results are reported, not asserted. `scan6000.txt` is the log of `scan.py 6000 1 2`.
  - `sym.py`: the Lemma 3.2 identities (symbolic).
  - `lemma_check.py`, `ostrowski_check.py`: Lemmas 3.1 and 5.2 (word identities).
  - `lam1_norm.py`, `lam1.py`: Lemma 5.1 (2-adic norms and trace valuations) and the finite part of Theorem 1.2.
  - `recheck.py`: independent of all the above: from the Laplacian matrices directly, deficits for `n ≤ 700` (numerically, with a gap-separation test), doubles at `n = 4F_k` against the twisted-cycle spectrum, and the finite part of Theorem 1.2 as the exact rank of `L_n − I` over `Q`.
  - `mutants.py`: after checking that every unmodified program passes (including an unequal-weight baseline for the equal-weight mutant), eleven planted wrong variants (transfer matrix, equal weights, exceptional sets, invariant, weights, word factor, decomposition, twist phase); each must be rejected, a timeout or crash counting as a rejection.
  - `oeis-A401899-snapshot.json`: the OEIS record as fetched on 20 November 2026.

## Reproduce

```
pip install numpy sympy python-flint
cd verify
python3 certify.py 13 1 2 && python3 certify.py 11 3 7/5          # about 1 min
python3 scan.py 6000 1 2 && for w in "3 7/5" "1 3" "2 5" "1 4"; do python3 scan.py 2000 $w; done   # about 2 min
python3 sym.py && python3 lemma_check.py && python3 ostrowski_check.py && python3 lam1_norm.py && python3 lam1.py
python3 recheck.py                                                 # about 35 s
python3 mutants.py                                                 # about 1 min; must print 11/11 mutants killed
cd ../paper && latexmk -pdf fibonacci-cycle.tex
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
