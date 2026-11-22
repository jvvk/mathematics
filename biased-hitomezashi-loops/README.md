# The loop density of biased random hitomezashi patterns

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/961957e77ad3106556b930df9aa1f48254a77269/assets/hitomezashi-biased.svg" width="760" alt="A biased hitomezashi pattern at p = 0.3 and the loop-density result"></p>

<p align="center"><b>Label every grid line 0 with probability p and stitch alternate segments. The expected number of closed loops per cell has a closed form for every p; the fair coin is the unique minimum.</b><br><sub>New result extending Defant and Kravitz (p = 1/2) · label lemmas and series evaluation in Lean · remaining steps by paper proof and exact checks</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

A hitomezashi pattern is drawn by labelling every line of an `m × n` grid `0` or `1` and stitching alternate unit segments of each line, starting according to its label. Defant and Kravitz (*Loops and regions in Hitomezashi patterns*, Discrete Math. 347 (2024) 113693) proved that with fair coin labels the expected number of closed loops is `((π² − 9)/12 + o(1)) mn`. Pete (Ann. Probab. 36 (2008), Section 7) had already observed that when every label is `0` with probability `p`, all components are still finite; no loop density was known for `p ≠ 1/2`.

This paper proves:

- **Theorem 1.1.** For every `p` in `(0, 1)`, with `q = 1 − p`, the loop density is

  `c(p) = 2pq − 5/4 + (π²p²q²/6)(2 + 3/sin²πp) + π pq (1 − 3pq) cot(πp) / (1 − 2p)`,

  with the value `(π² − 9)/12` at `p = 1/2`.
- **Theorem 6.1.** `c` strictly decreases on `(0, 1/2]` and strictly increases on `[1/2, 1)`, so the fair coin is the unique minimum, with an explicit lower bound on the cost of bias.
- **Theorem 6.2.** A closed form when the vertical and horizontal lines have different biases, with an explicit `O(N⁻³)` bound on the error of the truncated series.

The proof reads off the labels a loop forces from Pete's pair of Dyck paths, which turns the density into a sum over weighted Dyck paths of fixed height. The two-step transfer matrix of these weights has a double eigenvalue for every `p`, so the continuants are linear in the index and the sum reduces to Euler's partial fraction expansions of `cot` and `csc²`.

Preprint v1, 22 November 2026, not peer reviewed; released before the author's own line-by-line reading. Zenodo: [doi:10.5281/zenodo.24448300](https://doi.org/10.5281/zenodo.24448300), identical to this folder at tag `biased-hitomezashi-loops-v1`. What is verified how: the label lemmas (Lemmas 2.1 and 2.3), the continuant identities (Lemmas 4.3, 4.4, Proposition 4.5) and the evaluation of the density series (Theorem 1.1 from the series) are formalised in Lean 4 (`lean/`, standard axioms only). Pete's loop correspondence and the continued-fraction theorem are cited; the evaluation at `z = 1`, the limiting-density argument and Theorems 6.1 and 6.2 are paper proofs, checked by exhaustive enumeration, exact arithmetic and high-precision computation in `verify/`. The question of a closed form for `p ≠ 1/2` was posed by us; the model is Defant and Kravitz's and Pete's. The author used AI tools (Claude, Anthropic, to find the arguments and write the code, Lean and text; Codex, OpenAI, which corrected Lemma 2.3, contributed Theorem 6.1 and the truncation bound, and reviewed the release) and is responsible for the content.

## Contents

- `paper/`: `paper.tex` and `paper.pdf` (12 pp); `figs/` holds the figure inputs and the scripts that generate them.
- `verify/` (Python 3.11 or later; `mpmath` 1.3.0, see `../requirements.txt`):
  - `per_loop.py`: every labelling of the 7 × 7 grid; checks the forced-label reading on all 209,579 loop occurrences.
  - `closed_form.py`: truncated weighted Dyck-path sums and the evaluated height series against the closed form, including `p = 1/2`.
  - `monte_carlo.py`: seeded simulation against the finite-size expectation formula, evaluated in floating point (four-standard-error tolerance).
  - `two_parameter.py`, `extensions.py`: the two-bias formula, the exact polynomial certificate behind Theorem 6.1, and exact-rational truncation intervals for Theorem 6.2.
  - `mutants.toml` with `mutate.py`: 12 planted errors, each of which must make the unchanged checks fail; log in `mutation-log.txt`. A mutant counts as rejected only on a failed assertion; any other exception is reported as inconclusive.
  - `exponent_sim/`: the simulation behind the evidence for Question 6.4 (not a proof). `run.sh` compiles `loops.c`, traces every loop in 200 random 12000 × 12000 patterns at each `p` in {0.5, 0.4, 0.3, 0.2, 0.15} with fixed seeds 1 to 5, writes the histograms `big_<p>.txt`, and runs `fit2.py`, whose output is `fit2-output.txt`. A few minutes on five cores.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0, namespace `HitomezashiBiased`. `lean/README.md` maps each result to its Lean name; `CheckClaims.lean` prints the headline statements with their axioms; `scripts/mutants.toml` (run by `scripts/mutate.py`) holds 15 planted wrong changes, each of which must stop the build; `axiom-validation.txt` and `build-validation.log` record the isolated build.

## Reproduce

```
python3 -m venv .venv && . .venv/bin/activate && pip install -r requirements.txt
python3 verify/per_loop.py && python3 verify/closed_form.py && python3 verify/monte_carlo.py
python3 verify/two_parameter.py && python3 verify/extensions.py
python3 -I verify/mutate.py verify/mutants.toml          # 12 mutants, each rejected

cd paper && latexmk -pdf paper.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
python3 -I scripts/mutate.py scripts/mutants.toml        # 15 mutants, each rejected (slow)
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE). Mathlib is a pinned dependency (Apache-2.0), fetched by `lake`, not redistributed here.
