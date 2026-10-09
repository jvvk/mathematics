# Polynomial lemniscates meet in at most 2n₁n₂ − 2 points

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/c7403d6bbbc7106e1780d8c34833854afcb0116f/assets/lemniscates.svg" width="760" alt="Two figures of eight"></p>

<p align="center"><b>Polynomial lemniscates meet in at most 2n₁n₂ − 2 points; two lemniscates of Bernoulli in at most six.</b><br><sub>Open problem settled · formally verified in Lean 4</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Orevkov and Pakovich proved that two lemniscates |P₁| = ρ₁ and |P₂| = ρ₂ of rational functions of degrees n₁, n₂ meet in at most 2n₁n₂ points when they meet in finitely many, that this is sharp for rational functions, and remarked that it does not seem sharp for polynomials. The paper proves that two polynomial lemniscates of degrees n₁, n₂ ≥ 2 with finitely many common points have at most 2n₁n₂ − 2 of them. The bound is attained for (n₁, n₂) = (2, 2) and (2, 3), so the maximum there is 6 and 10. In particular two distinct Cassini ovals, and two lemniscates of Bernoulli, meet in at most six points, which answers [Mathematics Stack Exchange question 1250327](https://math.stackexchange.com/q/1250327) (2015). The proof treats z and z̄ as independent variables: the 2n₁n₂ complex solutions, counted with multiplicity, have a weighted sum equal to −(n₁n₂/2)|c₁ − c₂|² ≤ 0, which forces two of them off the real locus.

Preprint v1, 8 October 2026, not peer reviewed. Theorem 1, Corollaries 2 and 3 and every lemma are formally verified in Lean 4 (`lean/`, standard axioms only); the ten common points of the (2, 3) example are certified by interval arithmetic and rechecked by an independent program. The exposition has not yet been independently reviewed. The author used an AI tool (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf`, the figures `figs/six.pdf` and `figs/pairing.pdf`, and `abstract.txt`.
- `lean/`: its own Lake project, pinned to Lean 4.34.0 and the Mathlib revision in `lake-manifest.json`. `Lemniscates.theoremA` is Theorem 1; `Lemniscates.oval_le_six`, `Lemniscates.bernoulli_six` and `Lemniscates.M_eq_iff` are the corollaries; every lemma of the paper has a named counterpart (see `lean/README.md`). `CheckClaims.lean` prints each statement and its axioms (only `propext`, `Classical.choice`, `Quot.sound`); `axiom-validation.txt` is its saved output and `build-validation.log` records a fresh isolated build. `scripts/mutants.py` checks that 19 deliberately wrong variants fail to compile (`mutants-validation.txt`).
- `verify/`: `certify_points.py` certifies the 6 and 10 common points of the two sharp examples by the Krawczyk test in interval arithmetic; `recheck.py`, which shares no code with it, recomputes every complex solution of both examples from an exact resultant and confirms the counts, the trace identity and the numbers in Figure 2; `trace_symbolic.py` and `trace_identity.py` check the trace identity symbolically (degree 2, all coefficients free) and exactly for degrees (2, 3) and (3, 3); `figures.py` draws the figures. Saved outputs are in `verify/results`.

## Reproduce

```
cd lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
python3 scripts/mutants.py
cd ../verify && python3 certify_points.py && python3 recheck.py
python3 trace_symbolic.py && python3 trace_identity.py
cd ../paper && latexmk -pdf paper.tex
```

The Python checks need `mpmath`, `sympy`, `numpy` and `matplotlib` (tested with Python 3.14, mpmath 1.3.0, sympy 1.14.0).

## Licence

The paper and figures are released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
