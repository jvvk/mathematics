# Coins in a tray

<!-- visual:start -->
<p align="center"><img src="https://raw.githubusercontent.com/jvvk/jvvk/5b5d7970c5db2678ca44d9f45af5670e9e6ea95c/assets/coins-in-a-tray.svg" width="760" alt="Coins in a tray"></p>

<p align="center"><b>Coins of radii 1/2, …, 1/n cannot be held rigidly around the rim of a unit tray for any 5 ≤ n ≤ 1000: the rim angles are arguments of 1 − s√−a, and their relations are decided by prime-ideal valuations.</b><br><sub>Partial answer · searches exact, key lemmas in Lean</sub></p>

<p align="center"><sub><a href="paper">paper</a> · <a href="lean">Lean proof</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Dan asked on Mathematics Stack Exchange ([question 4940077](https://math.stackexchange.com/q/4940077)) and MathOverflow ([question 513668](https://mathoverflow.net/q/513668)) for which `n` coins of radii `1/2, 1/3, …, 1/n`, at least one of each, can be held rigidly in a circular tray of radius `1`. He found arrangements for `n = 2, 3, 4` and conjectured that there are none for `n ≥ 5`. This note settles two special cases:

- **Theorem 1.** For `5 ≤ n ≤ 1000` there is no rigid arrangement with every coin touching the tray. For `n = 5` the proof is by hand.
- **Theorem 2.** For `5 ≤ n ≤ 16` there is no arrangement whose contact graph, tray included, is a triangulation.
- **Proposition 3.** A coin `1/k` touching the tray and two coins that touch each other and the tray has `k ≡ 2, 3, 6, 11, 14, 15, 18, 23 (mod 24)`.

Two rim coins `1/j`, `1/k` subtend the angle `α_d` with `cos α_d = 1 − 2/d`, `d = (j − 1)(k − 1)`. Writing `d − 1 = s²a` with `a` squarefree, `α_d = π + 2 arg(1 − s√−a)`. By the splitting theorem of Conway, Radin and Sadun, a relation among these angles splits by class `a`. Within a class, a relation holds exactly when the prime-ideal valuations of the numbers `1 − s√−a` cancel at every split prime. This decides every relation exactly, so the searches use no floating-point relation test. The same test, applied to the angles around any coin, decides closed coronas and gives Theorem 2. Proposition 3 follows from the congruence theorem of Graham, Lagarias, Mallows, Wilks and Yan for Apollonian packings.

Preprint v1, 10 October 2026, not peer reviewed. The general question remains open. The rim angle formula, the Niven classification of rational rim angles, the asker's identity `2α₃ + α₉ = π`, the overlap in the `n = 5` proof and the uniqueness of the root quadruple `(−1, 2, 2, 3)` are formally verified in Lean 4 (`lean/`, standard axioms only). The splitting theorem and the congruence theorem are quoted, and the searches are Python computations, which by design stay outside Lean. The author used AI tools (Claude, Anthropic) in this work, as described in the paper's acknowledgement, and is responsible for its content.

## Contents

- `paper/`: `note.tex` and `note.pdf`; `figs/` holds the TikZ figure data written by `verify/figs.py`.
- `verify/`:
  - `exact.py`: the exact relation test. It factors the norm of `1 − s√−a` (or `p + s√−a` for corona angles), computes both prime-ideal valuations at each split prime through a `p`-adic square root of `−a`, and decides a relation by cancellation.
  - `check_relations.py`: compares the exact test with 60-digit numerics on 122,400 random combinations of rim angles. `MUTANT=1` deletes the prime 3 from every valuation vector and must print `FAIL`.
  - `rim_certify.py`: Theorem 1. For each `n` it first prunes by sign at split primes, and stops if some size is left with no possible rim neighbour (every `7 ≤ n ≤ 10` and `20 ≤ n ≤ 1000`). Otherwise it enumerates exact relations by class, combines them to exactly `2π`, and searches Euler circuits for a ring with no overlap. It reports truncations, near-tangencies and the smallest overlap margin. `MUTANT=1` replaces the exact test by rounding, which changes the output at `n = 12`.
  - `corona_certify.py`: Theorem 2. It finds every closed corona of every coin with the exact test, then lists the sizes that cannot be linked to the tray. `MUTANT=1` replaces the exact test by rounding, which changes the output at `n = 8`.
  - `corona.py`: geometry helpers for `corona_certify.py`; its own 80-digit search is an independent cross-check.
  - `apollonian.py`: Proposition 3. It finds the root quadruples with outer curvature `−1` and the residues mod 24 of the packing's curvatures up to 5000.
  - `figs.py`: Figures 1 and 2. It asserts that the asker's ring and the `1/7` corona close up exactly, and that the two halves in the `n = 5` argument overlap.
- `lean/`: a Lake project pinned to Lean 4.34.0 and Mathlib v4.34.0. `lean/README.md` maps results to Lean names, `CheckClaims.lean` prints their axioms, and `scripts/mutants.py` runs the mutation tests.

## Reproduce

```
cd verify && python3 check_relations.py && MUTANT=1 python3 check_relations.py | tail -1
python3 rim_certify.py 3 4 $(seq 5 22)      # small cases and the exhaustive range
python3 rim_certify.py $(seq 23 1000)       # pruning strands a size for every n here (about 40 minutes)
python3 corona_certify.py 5 8 12 16
python3 apollonian.py && python3 figs.py
cd ../paper && latexmk -pdf note.tex
cd ../lean && lake exe cache get && lake build LeanProofs && lake env lean CheckClaims.lean
```

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
