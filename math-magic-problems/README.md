# Seven problems from Erich Friedman's *Math Magic*

<!-- visual:start -->
<table>
<tr><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/bishops.svg" width="100%" alt="Three armies of bishops"><p><b>Three armies of bishops</b><br>Three armies of five bishops fit on a 5 × 5 board and three of eight on 6 × 6, and no more: Friedman's two values.<br><sub>Exhaustive count of diagonal labellings</sub></p></td><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/capture.svg" width="100%" alt="Chess capture patterns"><p><b>Chess capture patterns</b><br>Friedman's capture digraphs q, r and s are not made by any chess position, on any board.<br><sub>Two independent solvers</sub></p></td></tr>
<tr><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/kings.svg" width="100%" alt="Kings that touch in a cycle"><p><b>Kings that touch in a cycle</b><br>Kings with touch counts (1,3,6), (1,6,3) or (2,3,4) admit no finite arrangement: Friedman's unsolved problem 24.<br><sub>DRUP certificates, independent Z3 check</sub></p></td><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/heptomino.svg" width="100%" alt="A heptomino that never balances"><p><b>A heptomino that never balances</b><br>This heptomino never fills a square with equal row and column counts, in any size: one shape of Friedman's problem 15.<br><sub>Proof by hand, exact checker</sub></p></td></tr>
<tr><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/tournament.svg" width="100%" alt="A tournament schedule that beats the table"><p><b>A tournament schedule that beats the table</b><br>Friedman's optimal tournaments: exact best schedules over all adaptive plans, two of them better than the published values.<br><sub>Exact recursion, two programs</sub></p></td><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/prime-signature.svg" width="100%" alt="A misfiled prime signature"><p><b>A misfiled prime signature</b><br>In Friedman's prime-signature table, 1022303⁴ belongs in cell (4, 411), where it is the smallest; cell (4, 41) is empty.<br><sub>Proof by hand, computer search</sub></p></td></tr>
<tr><td width="50%" valign="top"><img src="https://raw.githubusercontent.com/jvvk/jvvk/a1ad1fff67d6b767c3139c447ca4f0f6890a199e/assets/slabs.svg" width="100%" alt="Cubes cut into slabs"><p><b>Cubes cut into slabs</b><br>A cube made of one k-slab for each k ≤ n has side at most n(n+1)/2, and none exists for n = 4, 5, 6; Friedman conjectures infinitely many.<br><sub>Bound by hand, n = 4 to 6 by two searches</sub></p></td></tr>
</table>

<p align="center"><sub><a href="paper">paper</a> · <a href="verify">code</a> · <a href="../">all results</a></sub></p>
<!-- visual:end -->

Erich Friedman's [Math Magic](https://erich-friedman.github.io/mathmagic/) poses a problem each month and keeps a [list of unsolved problems](https://erich-friedman.github.io/mathmagic/unsolved.html). As of 9 October 2026 the list shows problems 15, 21 and 24 as open, and the [March 2005 page](https://erich-friedman.github.io/mathmagic/0305.html) on armies of bishops asks for two exact values. The paper settles these four, and makes progress on problems 6, 28 and 33, which the list also shows as open:

- **Armies of bishops.** `B(3,5) = 5` and `B(3,6) = 8`: three armies of five bishops fit on a 5 × 5 board and three of eight on a 6 × 6 board, and no more. A placement is valid exactly when every diagonal carries one army, which turns the question into an exhaustive count over labellings of the diagonals.
- **Touch cycles (unsolved problem 24).** No finite arrangement of three colours of king has touch counts `(1,3,6)`, `(1,6,3)` or `(2,3,4)`, nor `(1,4,5)`. An extreme king reduces any finite arrangement to a finite formula, refuted with a DRUP certificate. Each listed triple does have a periodic arrangement of the whole plane, so finiteness is essential.
- **Capture digraphs (unsolved problem 21).** The 2-regular digraphs `q`, `r` and `s` on six points are not the capture graph of any chess position on any board.
- **Magic polyomino squares (unsolved problem 15).** The first listed heptomino can never be arranged in a square with equal row and column counts. The proof is an explicit weighting of rows and columns.
- **Slab cubes (unsolved problem 6).** A cube tiled by one `k`-slab (a `k × ik × jk` box) for each `k = 1, …, n` has side at most `n(n+1)/2`, with equality only for `n = 1, 3`; no such cube exists for `n = 4, 5, 6`. The bound is proved; the non-existence is certified by two programs, one with a constraint solver and one without.
- **Prime signatures (unsolved problem 28).** The table's entry `1022303⁴` in cell `(4,41)` belongs in cell `(4,411)`, where it is the smallest value (proved, using Ljunggren's theorem on `x² + 1 = 2y⁴`); cell `(4,41)` is empty. The two open cases have no solution below `10¹⁷`.
- **Optimal tournaments (unsolved problem 33).** Exact optima over all adaptive schedules: ranking 3 players in 7 games succeeds with probability `2992/6561` (published `2944/6561`), 4 players in 7 games with `1216/6561` (published `1136/6561`); three entries for 5 players are corrected, and every other published value checked is optimal.

Preprint v2, 9 October 2026 (v1 the same day had the first four results), not peer reviewed. Some results are computer-certified and some proved by hand; the paper says which, and for each certified result what was computed, why it suffices, and how it was checked independently. No Lean formalisation: the certified results are exhaustive counts and solver refutations, checked by certificates and by programs written independently. The author used AI tools (Claude, Anthropic; Codex, OpenAI) in this work, as described in the paper, and is responsible for its content.

## Contents

- `paper/`: `paper.tex`, `paper.pdf`, and `make_figs.py`, which draws every figure from the data in `verify/` and checks it as it does so (the bishop armies are valid, every touch count holds, the capture position is 2-regular).
- `verify/bishops/`: `check.py` verifies both placements with an attack simulator and counts every labelling of the diagonals (standard library, seconds); `mutants.py` checks that two deliberate errors change the answers.
- `verify/touch-cycles/`: `certificates/` holds the four CNF formulas with DRUP refutations; `verify_drup.py` checks them (standard library); `touch_extreme.py` is an independent Z3 encoding of the same window problems, with controls; `touch_torus.py` finds the periodic arrangements; `PROOF.md` and `HUMAN-PROOF-145.md` give the reduction and the hand proof for `(1,4,5)`; `certify.py` regenerates the certificates.
- `verify/capture-digraphs/`: `src/` enumerates the 23 digraphs and decides each with Z3 (`realize.py`); `verify/second.py` is an independent cvc5 model; `verify/check.py` is a square-by-square simulator; `verify/test_*.py` test the encodings against it with mutants; `out/` holds the solver logs and the transcribed published positions.
- `verify/heptomino/`: `check_shapeA.py` checks the weights in exact arithmetic for every side from 5 to 400 and the induction step symbolically, and rejects four mutants; `PROOF.md` is the proof in brief.
- `verify/slab-cubes/`: `slabs.py` and `slabs_cube.py` refute every volume-feasible choice of slab sizes with an exact-cover model in OR-Tools CP-SAT (progress records in `data/`); `slab_search.py` decides the same cases with no solver, by a corner-first search with volume pruning, and finds the known tilings as controls (`slab_search_sweep.log`: all 29 cube sides for `n = 4, 5, 6`, about an hour in total); `slab_mutant.py` checks that a weakened search (any `k × i × j` box) does find tilings, so the negatives are not vacuous.
- `verify/prime-signatures/`: `primesig_4_411.py` finds the smallest value in cell `(4,411)` (needs `sympy`); `primesig_pairs.py` lists the two open cases to `10^X` (`data/primesig_pairs_17.txt` is the run to `10¹⁷`); `test_primesig_pairs.py` checks those lists against brute force; `primesig_table.py` checks all 650 published values.
- `verify/tournaments/`: `tournament.py` computes the optima by an exact integer recursion; `tournament_check.py` is a separate exact-rational program with simulation; `tournament_table.py` compares with the published tables (`data/tournament_published.json`).

## Reproduce

Python 3.10 or later. The capture-digraph models need `pip install -r verify/capture-digraphs/requirements.txt` (Z3 and cvc5); the touch-cycle cross-check needs `z3-solver`. Everything else uses the standard library.

```
cd verify/bishops && python3 check.py && python3 mutants.py
cd ../touch-cycles && python3 -B verify_drup.py
python3 touch_extreme.py 1 3 6 0 1 6; python3 touch_extreme.py 1 6 3 0 1 6
python3 touch_extreme.py 2 3 4 1 1 8; python3 touch_extreme.py 1 4 5 0 1 4
python3 touch_extreme.py 1 2 3 0 1 6   # control: sat
python3 touch_torus.py 1 3 6 6; python3 touch_torus.py 1 6 3 8; python3 touch_torus.py 2 3 4 6
cd ../capture-digraphs && python3 src/realize.py && python3 verify/second.py && python3 verify/test_encoding.py
cd ../heptomino && python3 check_shapeA.py 400
cd ../slab-cubes && python3 slab_search.py 3 6 6 6 && python3 slab_search.py 5 10 10 10   # control: tiling; then none
cd ../prime-signatures && python3 primesig_4_411.py 1022303 && python3 test_primesig_pairs.py && python3 primesig_table.py
cd ../tournaments && python3 tournament.py rank 3 7 && python3 tournament_check.py rank 3 7
cd ../../paper && python3 make_figs.py && latexmk -pdf paper.tex
```

On a laptop the DRUP check takes about 13 seconds, the bishop count a few seconds, and each solver run seconds to a minute.

Friedman's pages had not recorded these results when this was released, and he has not reviewed them.

## Licence

The paper is released under [CC BY 4.0](../LICENSE-PAPERS), the code under the [MIT licence](../LICENSE-CODE).
