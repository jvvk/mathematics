# Agreement subtrees of balanced trees

Two rooted binary trees on the same leaf labels agree on a set of labels when the subtrees they induce on
it are the same. Let `M(n)` be the least possible size of the largest such set over all pairs of
*balanced* trees on `n = 2^m` leaves. Martin and Thatte conjectured `M(n) ≥ √n`; Bordewich, Linz, Owen,
St. John, Semple and Wicke (SIAM J. Discrete Math. 2022) disproved it by a slowly vanishing factor and
proved `M(n) ≥ n^0.17`.

The paper proves:

- **The exponent exists.** A substitution lemma makes `M` submultiplicative, so by Fekete's lemma
  `β = lim log₂ M(2^m) / m` exists and equals the infimum. Any single pair of balanced trees therefore gives
  a bound for all `n`.
- **`β ≤ 5/11`.** The `k = 3` example of Bordewich et al. (2048 leaves, agreement 32) gives
  `M(n) ≤ 2^10 n^(5/11)`, polynomially below `√n`.
- **`β ≥ 0.243`.** Their inductive lower bound with optimised constants gives `n^0.235`; an induction
  that looks two levels down one tree and one level down the other gives `n^0.243`.

Preprint v1, 9 October 2026, not peer reviewed.

- **Formally verified in Lean 4** (`lean/`, standard axioms only):
  - the substitution lemma, submultiplicativity and the existence of the exponent;
  - Lemma 4.5 of Bordewich et al. and an explicit 2048-leaf pair with agreement at most 32, hence
    `β ≤ 5/11`;
  - `M(n) ≥ n^0.235`, including its computer-assisted inequality (Lean checks a certificate);
  - the two-level induction, giving `M(n) ≥ n^0.243` from the inequality of Lemma 5.3;
  - that agreement through triples is the usual definition (`S|Y ≅ T|Y`).
- **Not formalised:** the inequality of Lemma 5.3. Its certificate (1,418,968 simplices) is checked in
  exact arithmetic by `verify/certify_simplex_rig.py`. So `n^0.243` rests on that program, while `n^0.235`
  and `5/11` are fully machine-checked.

The author used an AI assistant (Claude, Anthropic) in this work, as described in the paper's
acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, and the two figures with the scripts that draw them.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean
  names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.
- `verify/`: the certifiers, the dynamic program for `mast`, and the generators of the Lean certificate
  data; `verify/README.md` lists what each checks.

## Reproduce

```
cd verify
python3 mast.py
python3 certify_iv.py 2/5 33/400
python3 certify_simplex_rig.py 2,1 2/5 157/2000      # about 10 minutes
cd ../paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
