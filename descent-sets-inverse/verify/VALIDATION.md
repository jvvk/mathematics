# Validation of the 7 October 2026 revision

The manuscript compiled successfully with latexmk/pdflatex. Every page of the
final PDF was rendered and visually inspected. No overfull boxes or undefined
references were reported in the final LaTeX log.

## Formal source validation

An isolated project containing exactly the archived local import closure was
built from source: `lake build LeanProofs` completed successfully (3865 jobs).
Its local build directory was initially empty. The pinned dependencies and
Mathlib cache were supplied from the existing local package cache; dependency
network retrieval was not tested. Existing linter/deprecation warnings do not
prevent successful compilation. See `lean/build-validation.log`.

`lake env lean CheckClaims.lean` completed successfully. The saved signatures
and axiom lists are in `lean/axiom-validation.txt`: only propext,
Classical.choice and Quot.sound occur. The theorem parameters must also be
read: JoCG Theorem 2 retains its explicit enumeration hypothesis; the EJC
main theorems are unconditional. The packages contain no build caches.

## Fresh finite checks

- All illustrated examples passed.
- All 339,296 constructed row words through n=16 passed the shape, descent
  and lattice-word checks.
- Direct permutation enumeration through n=9 confirmed every certified pair.
- Shape-support intersections agreed pair by pair with dominance-interval
  intersections through n=13, including all 16,777,216 ordered pairs at n=13.
- Diagonal maxima through n=14, the local maximum at n=11 and the stated
  table strata passed. The rounded n=12, difference-5 table entry is corrected
  to 0.015 (exact proportion 0.015479876...).
- Seed-11 sampling at all seven recorded sizes was repeated with 20,000 pairs
  per size, and exact rational generating-function calculations through n=160
  were repeated. Outputs are in results/.

All assertions passed. These finite computations do not prove the open
conjectures beyond their stated ranges.

## Formalisation continuation

The current source graph was freshly compiled into an isolated directory:
35 modules passed with the original project module cache
excluded. Twenty selected theorem/finite-control axiom audits passed, with
only standard axioms. No sorry, admit or axiom declaration was found in the
compiled local source graph. The standalone archive is built separately with
its updated root and claim driver; saved output is in lean/. No new Python
computations were performed in this continuation.

## 8 October 2026 update

Added LowerGap.lean (Remark 3.4 lower bound), TwoBlocks.lean (its import) and
GrowthForward.lean (converse of Lemma 2.1). Source commit d811d08; no
uncommitted overrides. A fresh isolated copy of lean/ with an empty local
build directory compiled with `lake build LeanProofs` (3871 jobs).
`lake env lean CheckClaims.lean` exited 0; all 15 axiom reports list only
propext, Classical.choice and Quot.sound (lean/axiom-validation.txt). No sorry,
admit, axiom declaration or native_decide occurs in lean/LeanProofs. In the
development project, mutation tests 27-32 for these modules were all rejected
by Lean. The manuscript's Section 6 was updated to match; no Python
computation was rerun.

## 8 October 2026, second update

Theorem 1.1 now has rate 1/150 (DensitySharp.lean) and Remark 3.4 the bound
f(n) <= 4^(n-1) - 3^(n-1) + 1 (BlockObstruction.lean). Source commit recorded in
lean/SOURCE-SNAPSHOT.json, no uncommitted overrides. A fresh isolated copy of lean/
compiled with `lake build LeanProofs` (3873 jobs); `lake env lean CheckClaims.lean`
exited 0 with 19 axiom reports, all propext, Classical.choice and Quot.sound. Mutation tests
33-39 for these modules were rejected by Lean in the development project. The archived
gr_fail.cpp reproduced the saved n = 24 value exactly and gives 0.026547 at n = 20, half of
the exact failure proportion 1 - f(20)/4^19 = 0.053094; block_comp.py reproduced the saved
comparison table.

## 8 October 2026, third update (journal-ready fixes)

Added DominanceNecessity.lean and its two imports; isolated rebuild 3876 jobs; 21 axiom reports,
all standard. Added the independent programs and outputs under computations/independent and
results/independent. recheck.py: all claims pass after the two rounding corrections now in the
paper (0.9995, 0.00098). gr_check.c reproduces 0.026547 (n=20), 10.66 (n=24), 20.38 (n=44).
