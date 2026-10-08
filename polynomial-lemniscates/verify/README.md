# Verification programs

Run from this folder; each exits nonzero on failure and prints `ALL PASS` (or `exit 0`) on success. Saved outputs are in `results/`.

| Program | Checks |
|---|---|
| `certify_points.py` | The (2,2) example z² − 1, (z − 1)² − 1 and the (2,3) example (z − 1/10)² − 1, z³/8000 − 1 (levels 1): 6 and 10 pairwise disjoint boxes, each certified by the Krawczyk test (mpmath interval arithmetic, 50 digits) to contain exactly one common point. Together with Theorem 1 this gives Corollaries 2 and 3. |
| `recheck.py` | Independent of the above: eliminates W exactly (sympy resultant), finds all 2n₁n₂ complex solutions of both examples to 60 digits, counts the real ones (6 and 10), checks the trace identity (2) (−2 and −3/100), the closed forms in Figure 2, and the values of M(n₁, n₂) in Corollary 3 and Remark 14. |
| `trace_symbolic.py` | Identity (2) for n₁ = n₂ = 2 with all eight coefficients and both levels free: the trace over Q(parameters)[Z,W]/(F₁,F₂) via a Gröbner basis. |
| `trace_identity.py` | Identity (2) exactly, by Gröbner bases, for random rational data of degrees (2,2), (2,3), (3,3). `MUTANT=1` plants a wrong right-hand side, which must fail (`results/trace_identity_mutant.txt`). |
| `figures.py` | Draws `../paper/figs/six.pdf` and `../paper/figs/pairing.pdf`, and checks the numbers shown in Figure 2. |
