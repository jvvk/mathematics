# Mathematics

Papers and notes by Vamshi Jandhyala, each with the code that checks it. Every folder is self-contained: `paper/` holds the source and PDF, `verify/` the checks, and `lean/` a Lean 4 formalisation where there is one, as its own Lake project pinned to the Mathlib version it was checked with.

| Result | Kind | Status | Verified |
|---|---|---|---|
| [Descent sets of a permutation and its inverse: almost every pair occurs](descent-sets-inverse/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every proved result: Theorems 1.1, 1.2 and 3.6, Lemma 2.1 both ways, Lemma 3.5, Corollary 3.7); every stated number by independent programs |
| [Does the smallest enclosing copy fit? Random points in a convex polygon](smallest-enclosing-copy/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every theorem, lemma and corollary); numerical values by independent programs |
| [A mex sequence that is not ultimately periodic](mex-sequence-not-periodic/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every lemma and theorem, by two routes); every quoted number by an exact checker |
| [Infinitely many integers that are not quotients of zero-free balanced ternary numbers](balanced-ternary-quotients/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorems 1.1 and 1.3; generated proofs, core Lean); every quoted number by an exact checker; independent symbolic checker for Theorem 1.1 |
| [Tiling almost-squares with smaller distinct almost-squares](almost-square-tilings/) | Paper | Preprint, 8 October 2026; not peer reviewed | Independent checker for every finite case; Lean (Theorem 1, every lemma and printed number; n = 16, 17, 19 by `native_decide`) |
| [Two triangulations that share only their hull](two-triangulations-hull/) | Paper | Preprint, 8 October 2026 | Exact checker; exhaustive order-type search to n = 10; Lean (Theorem 2 assumes the n = 6 to 8 search) |
| [Shuffle anti-squares of every even length from 24](shuffle-anti-squares/) | Paper | Preprint, 8 October 2026 | Lean (Theorems 2 and 4, Corollary 6, all examples); exhaustive searches each confirmed by a second, independent program |
| [Six circles in a rectangle: a proof by pure geometry](six-circles-rectangle/) | Note | Preprint, 8 October 2026 | Every step checked numerically to 50 digits; Lean, step by step |
| [Nine rectangles of equal perimeter, no two alike, in a square](equal-perimeter-rectangles/) | Note | Preprint, 8 October 2026 | Exact rational enumeration of every type to n = 9 by two independent programs; counts match OEIS A100664 |

Papers and figures are released under [CC BY 4.0](LICENSE-PAPERS), code under the [MIT licence](LICENSE-CODE).
