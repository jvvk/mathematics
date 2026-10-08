# Validation of the 7 October 2026 revision

The manuscript compiled successfully with latexmk/pdflatex. Every page of the
final PDF was rendered and visually inspected. No overfull boxes or undefined
references were reported in the final LaTeX log.

## Formal source validation

An isolated project containing exactly the archived local import closure was
built from source: `lake build LeanProofs` completed successfully (3126 jobs).
Its local build directory was initially empty. The pinned dependencies and
Mathlib cache were supplied from the existing local package cache; dependency
network retrieval was not tested. Existing linter/deprecation warnings do not
prevent successful compilation. See `../lean/build-validation.log`.

`lake env lean CheckClaims.lean` completed successfully. The saved signatures
and axiom lists are in `../lean/axiom-validation.txt`: only propext,
Classical.choice and Quot.sound occur. The theorem parameters must also be
read: Theorem 2 retains its explicit enumeration hypothesis; Theorem 1 is
unconditional. The packages contain no build caches.

## Fresh finite checks

- The independent exact checker passed all examples, the nine certificates,
  seven witnesses, convex seeds and the OCT comparison on 247 small sets.
- The C exact search was compiled and run on every supplied database order
  type for n=4 through 8. Minima: 4,5,6,6,6.
- Pentagonal-hull rows for n=6,7,8 contain 3,22,570 order types, respectively,
  and none permits exactly five shared edges. Inputs are identified by hashes.
- The larger n=9 and n=10 searches were not rerun in this revision. Their
  previously recorded results are preserved, explicitly distinguished from
  the fresh small-search output. The order-type database is not redistributed.

All assertions passed. These finite computations do not prove the open
conjectures beyond their stated ranges.

## 8 October 2026 revision

The manuscript was simplified: the general regeneration lemma for good pairs was replaced by a chain
(Definition 7) and a one-paragraph regeneration lemma (Lemma 8), matching `TwoTri.Inv` and `TwoTri.step`.
The Lean sources are unchanged; `CheckClaims.lean` now also prints `TwoTri.step`. The exact checker gained
section 9 (chains: the nine-point chain and its successor (56p; 347, 47p), the convex chain for h = 7..30, no
chain for h = 6, the seven-point chain, and 221 sampled insertions showing the hexagon seed loses its good
pair); its new checks were mutation-tested (5/5 failing mutants detected).
