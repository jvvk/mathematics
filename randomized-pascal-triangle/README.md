# A randomized Pascal triangle whose average blows up

Build Pascal's triangle, but let each interior entry be the sum of the two entries above it with probability `p` and their absolute difference otherwise. Does the expected average of all the entries tend to infinity? The question was asked on Mathematics Stack Exchange ([question 4972093](https://math.stackexchange.com/q/4972093)) and MathOverflow ([question 479618](https://mathoverflow.net/q/479618)); it was known for `p > 1/2`.

The expected sum of row `n` is at least `λ(p)^n` with `λ(p) = p² + √(p⁴ + 4p(1 − p))`, which exceeds 1 exactly when `p > 1 − 1/√2 ≈ 0.293` (Theorem 1). The proof uses the row sum and the total variation of the row: the sum grows only when the row is rough, and coins that disagree keep it rough. A computer-assisted extension of the same idea, with an exact certificate, gives growth for `p ≥ 29/125 = 0.232` (Theorem 2). In both ranges the expected average tends to infinity. Whether it stays finite for any `p > 0` is open; simulations by Einar Rødland on the Stack Exchange thread suggest it diverges for every `p > 0`.

Preprint v2, 9 October 2026, not peer reviewed (v1, 8 October 2026, verified Theorem 2 in Lean only relative to the certificate). Both theorems and the corollary are formally verified in Lean 4 (`lean/`, standard axioms only), including the local inequality behind Theorem 2: Lean checks the certificate on each of the 688 sign regions of its hyperplane arrangement. The certificate is also checked by two programs that share no code. The author used AI tools (Codex, OpenAI; Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps each result of the paper to its Lean name; `CheckClaims.lean` prints the axioms of every headline result; `scripts/mutants.py` runs the mutation tests.
- `verify/`: the certificate behind Theorem 2.
  - `certificate.py` (with `rays.py`) builds the hyperplane arrangement, its 251 extreme rays in the nonnegative orthant and the 1004 Bernstein coefficients, and writes `certificate.json`.
  - `verify.py` rebuilds the arrangement by exact symbolic simplex intersections, checks every polynomial, checks the triangle's exact distribution through row 6, and rejects three false certificates (`validation.json`).
  - `recheck/recheck.py` is an independent recheck sharing no code with the two above: it derives the arrangement from the definition of `G_p`, checks every Bernstein coefficient, verifies the window identity by enumerating every coin outcome on random rows, and rejects four false certificates. Standard library only.
  - `lp_explore.py` is the exploratory linear program behind the Remark in Section 5. Its thresholds are sampled, not certified.

## Reproduce

```
cd verify
python3 recheck/recheck.py        # independent recheck, about a minute
python3 certificate.py            # regenerates certificate.json (NumPy)
python3 verify.py                 # second check (SymPy)
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean   # the certificate files take about 40 minutes
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
