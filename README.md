# Mathematics

Papers and notes by Vamshi Jandhyala, each with the code that checks it. Every folder is self-contained: `paper/` holds the source and PDF, `verify/` the checks, and `lean/` a Lean 4 formalisation where there is one, as its own Lake project pinned to the Mathlib version it was checked with.

| Result | Kind | Status | Verified |
|---|---|---|---|
| [Two triangulations that share only their hull](two-triangulations-hull/) | Paper | Preprint, 8 October 2026 | Exact checker; exhaustive order-type search to n = 10; Lean (Theorem 2 assumes the n = 6 to 8 search) |
| [Six circles in a rectangle: a proof by pure geometry](six-circles-rectangle/) | Note | Preprint, 8 October 2026 | Every step checked numerically to 50 digits; Lean, step by step |

Papers and figures are released under [CC BY 4.0](LICENSE-PAPERS), code under the [MIT licence](LICENSE-CODE).
