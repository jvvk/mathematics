# A periodic twelve-fold tiling by the Spectre

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/748c75ff013f33057710b769112285f3a525f932/assets/spectre.svg" width="760" alt="A periodic twelve-fold tiling by the Spectre"></p>

<p align="center"><b>The Spectre tiles the plane only non-periodically, but 54 rotated and translated copies, repeated by a lattice, cover almost every point exactly 12 times: a periodic 12-fold tiling, with no reflections.</b><br><sub>Question answered · straight Spectre in Lean; curved Spectres by the same certificate</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

The Spectre of Smith, Myers, Kaplan and Goodman-Strauss ([Combinatorial Theory 4(2), 2024](https://doi.org/10.5070/C64264241)) tiles the plane by rotations and translations, and every such tiling is non-periodic. Andrew Bayly asked on MathOverflow ([question 516016](https://mathoverflow.net/q/516016)) whether it admits a periodic `n`-fold tiling for some `n > 1`, in which almost every point lies in exactly `n` tiles.

- **Theorem 1.** Yes, with `n = 12`: the tiles `ζ^r S + x a + y b + λ`, `λ ∈ Λ = ℤv + ℤw`, for 54 triples `(r, x, y)` listed in the paper (`ζ = e^{πi/6}`). It holds for the straight-edged `Tile(1,1)` and for every curved Spectre of the common-curve family. No reflections are used and no two tiles coincide; generic translates give every multiplicity `12m`.
- **Lemma 2**, the certificate: the 756 edges of one period cell cancel in 378 oppositely oriented pairs modulo `Λ`, a finite check in `ℤ[ζ]`. That makes the covering number constant; comparing areas, `54 (3 + 3√3) / (27/2)(1 + √3) = 12`.

Whether some `1 < n < 12` is possible is open.

Preprint v1, 20 October 2026, not peer reviewed. For the straight-edged Spectre the theorem is formally verified in Lean 4 (`lean/`, standard axioms only); for curved Spectres the edge-record certificate is kernel-checked but the step to constant coverage, which needs the Jordan curve theorem, is not formalised. The construction was found with OpenAI Codex and the Lean formalisation and checks were written with Claude (Anthropic), as described in the paper's acknowledgements; the author is responsible for the content.

## Contents

- `paper/`: `spectre-twelve-fold.tex`, `spectre-twelve-fold.pdf`, and `coverage_map.png` (Figure 2, written by `verify/coverage_map.py`).
- `verify/`:
  - `certificate.json`: the 54 placements `[r, x, y, 1]` and the matrix `K`.
  - `verify.py`: exact check in integer arithmetic, standard library only: the kernel of `K`, the 378 + 378 curved-edge records, both areas, and the multiplicity 12. Under a second.
  - `recheck_cover.py`: independent of `verify.py`: builds the straight 14-gon in floating point, adds every lattice translate near each sample point, and counts tiles at 20,000 random points of a period cell by the even-odd rule; all counts must be 12. About a minute. `MUTANT=1` drops one placement and must end in `FAIL`.
  - `coverage_map.py` (numpy, matplotlib): counts a curved Spectre over a 700 × 514 grid of four period cells (all 359,800 counts are 12) and draws Figure 2. An illustration, not a proof.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0; `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 verify.py && python3 recheck_cover.py && MUTANT=1 POINTS=300 python3 recheck_cover.py | tail -1
cd ../paper && latexmk -pdf spectre-twelve-fold.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
