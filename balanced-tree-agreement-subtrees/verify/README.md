# Verification scripts

Run every script from this folder. Python 3; `certify_simplex_rig.py` also needs numpy and scipy, and
`certify_iv.py` needs mpmath.

| Script | What it checks |
|---|---|
| `mast.py` | Exact dynamic program for `mast` of two balanced trees, based on recurrence (1); checks itself against brute force on 300 random pairs, rebuilds the construction of Bordewich et al. (agreement exactly 32 on 2048 leaves) and substituted pairs (exact product bound), and catches a broken construction (caterpillars not reversed: 128). |
| `verify_published.py` | Parses the two 2048-leaf trees printed in Bordewich et al., Appendix A, and computes their `mast` (32). Needs the text of arXiv:2005.07357: `mkdir refs && curl -L https://arxiv.org/pdf/2005.07357 -o refs/blossw.pdf && pdftotext refs/blossw.pdf refs/blossw_raw.txt`. |
| `certify_iv.py a c` | Lemma 5.1 by interval arithmetic with exact rational `a`, `c`: `python3 certify_iv.py 2/5 33/400` succeeds (4373 boxes); `2/5 2/25` fails, as it should. |
| `certify_simplex_rig.py DS,DT a c` | Lemma 5.3: `python3 certify_simplex_rig.py 2,1 2/5 157/2000` succeeds (1,418,968 simplices, about 10 minutes); `2,1 2/5 19/250` finds a violating vertex. With `1,1 2/5 33/400` it reproduces Lemma 5.1. Output of the full run: `cert_rig_21_2-5_157-2000.log`. |
| `strategies.py` | Generates the lookahead strategies from recurrence (1): 42 for the (2,1) case. |
| `test_rig_bounds.py` | Checks the exact lower bounds for `x^(2/5)` against 60-digit values; an inflated bound is rejected. |
| `lower2.py` | Numerical optimum of the one-level induction (about 0.2354). |
| `mast2.py` | Exhaustive search behind the remark on pairs with no common triple (`r = 5, 6, 7`). |
| `caterpillars.py` | Sixteen 8-caterpillars packing the balanced tree of height 7, by the recursion of Bordewich et al., Lemma 4.3; used by `../lean/LeanProofs/BalancedMast/Example.lean`. |
| `gen_strats.py` | The 42 strategies as Lean terms, by the same recursion; checks that they equal those of `strategies.py`, in order. |
| `cert_one.py` | The integer certificate for Lemma 5.1 that Lean checks (1638 boxes on the grid `1/2^16`). |

Lemma 5.1 is thus checked twice, by `certify_iv.py` and by Lean on an independently generated certificate.
Lemma 5.3 is checked once, by `certify_simplex_rig.py`: a floating-point search whose every accepted simplex
is rechecked in exact integer and rational arithmetic.
