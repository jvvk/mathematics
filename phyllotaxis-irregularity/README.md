# Irregularity versus growth rate in disk-stacking phyllotaxis

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/0a1e782c4f3e2922e57f95e2e3318993197ad0c5/assets/phyllotaxis.svg" width="760" alt="Irregularity versus growth rate in disk-stacking phyllotaxis"></p>

<p align="center"><b>In the disk-stacking model of phyllotaxis, no separate bounds on irregularity, notch angle and growth rate guarantee a Fibonacci transition: near every single-notch hexagonal front <code>D^mU^n</code> (2 ≤ m, n; n/2 < m < 2n) there is an explicit cone of slightly perturbed fronts whose very first disk makes a pentagon.</b><br><sub>Partial answer to the Golé–Dumais–Douady conjecture · first-order lemmas in Lean; first-disk theorem by hand</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Disks representing young organs are stacked on a cylinder, each new disk at the lowest position where it touches two disks already present and overlaps none; slowly decreasing diameters can produce the Fibonacci sequence of parastichy numbers `(1,2) → (3,2) → (3,5) → (8,5) → ⋯`. Golé, Dumais and Douady (Acta Soc. Bot. Pol. 2016, p. 30) conjectured that for each parastichy pair and each `N` there are tolerances on irregularity, notch angle and rate of diameter decrease, set independently, under which every front undergoes `N` Fibonacci transitions.

This paper proves:

- **Theorem A (pentagon on the first disk).** For every single-notch hexagonal front `D^m U^n` with `m, n ≥ 2` and `n/2 < m < 2n`, an explicit open cone of perturbations, with both directional deviations and the rate tending to zero and all initial disks obeying the diameter law, makes the first placement a pentagon transition. **Corollary 1.1:** there is no independent tolerance box, so the conjecture fails in its initial Fibonacci form (it is not ruled out after an unrestricted transient).
- **Theorem B (first transition).** From the three-disk fronts `F(β, ε)` the first transition completes with two triangle transitions and no pentagon, for small irregularity and rate.
- **Proposition 5.2 (frozen shape).** During a rhombic phase of `L` placements, ratios within either vector family change by `O(|c| + c²L)`.
- Uniform first-order formulas for rhombus and triangle steps (Section 3), and simulations from three-disk fronts suggesting a crossover controlled by the ratio of mismatch to rate (Section 8). **Conjecture C** (delayed pentagon): a first-order event calculation supports breakdown at the second transition when the mismatch exceeds a constant times the rate, but its transfer to the nonlinear dynamics is open.

Preprint v2, 24 October 2026 (v1: 20 October 2026), not peer reviewed; a specialist's independent review of the first-disk and first-transition arguments is still owed. Lean 4 verifies the local identities, the first-order lemmas and the frozen-shape estimate listed in `lean/README.md` (standard axioms only); the periodic first-disk argument, the uniform remainders and the candidate enumerations are proved by hand or certified in exact or interval arithmetic in `verify/`. Two AI tools were used in this work under the author's direction (Claude, Anthropic, and Codex, OpenAI), as described in the paper's acknowledgements, and the author is responsible for its content.

**Version 2** (24 October 2026, tag `phyllotaxis-irregularity-v2`): a referee report (Codex) found that the proof of Theorem B missed near-ties between triangles on down vectors and the intended placements, and one two-down triple. A new lemma (Lemma 6.1, shared contact, proved by Codex and checked by Claude) and the margin (12) close the gap; Theorem B stands as stated. Also: the triangle threshold is `120° + O(|c|)`, Theorem A is stated for single-notch fronts `D^m U^n`, the Lean coverage of Lemma 3.1 is stated exactly, the recorded outputs are shipped, and every proof check in `verify/README.md` exits nonzero on failure (`verify/down_triangle_exclusion.py` is new; the explorations are records).

## Contents

- `paper/`: `phyllotaxis-irregularity.tex` (with `sec_static.tex` and the `fig_*.tex` figure data) and `phyllotaxis-irregularity.pdf`.
- `verify/` (Python 3 with SymPy and mpmath): the checks behind each result, the two independent simulators and the recorded outputs (`.out`); `verify/README.md` maps each script to the result it checks and separates proof checks from explorations.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the 63 mutation tests.

## Reproduce

```
cd verify && python3 static_lattice_order.py && python3 static_23_proof.py && python3 static_general.py && python3 static_channel.py
python3 exact_limits.py && python3 certify_limits.py && python3 rhombic_step_formula.py && python3 triangle_step_formula.py
python3 review_independent.py && python3 simulators_agree.py
cd ../paper && latexmk -pdf phyllotaxis-irregularity.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

The proof checks above take under a minute together. The sweeps behind Section 8 (`break_probability*.py`, `critical_ratio.py`, `multi_step.py`) run for hours; their outputs are recorded in the `.out` files.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
