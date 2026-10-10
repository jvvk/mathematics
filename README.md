# Mathematics

Papers and notes by Vamshi Jandhyala, each with the code that checks it. Every folder is self-contained: `paper/` holds the source and PDF, `verify/` the checks, and `lean/` a Lean 4 formalisation where there is one, as its own Lake project pinned to the Mathlib version it was checked with.

<!-- visual:start -->
### Open problems settled, formally verified

Each result is checked end to end in Lean 4.

<table>
<tr>
<td width="50%" valign="top">
<a href="almost-square-tilings"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/almost-squares.svg" width="100%" alt="Almost-squares in almost-squares"></a>
<p><b><a href="almost-square-tilings">Almost-squares in almost-squares</a></b><br>
Which k × (k+1) rectangles split into smaller distinct ones: exactly 4, 10, 12, 14, 15, 18 and every k ≥ 20. Friedman's conjecture.<br>
<sub><a href="almost-square-tilings/paper">paper</a> · <a href="almost-square-tilings/lean">Lean</a> · <a href="almost-square-tilings/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="two-triangulations-hull"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/triangulations.svg" width="100%" alt="Two triangulations, one outline"></a>
<p><b><a href="two-triangulations-hull">Two triangulations, one outline</a></b><br>
From nine points on, two triangulations can share nothing but the five outline edges, answering Rote.<br>
<sub><a href="two-triangulations-hull/paper">paper</a> · <a href="two-triangulations-hull/lean">Lean</a> · <a href="two-triangulations-hull/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="smallest-enclosing-copy"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/enclosing.svg" width="100%" alt="Does the smallest copy fit?"></a>
<p><b><a href="smallest-enclosing-copy">Does the smallest copy fit?</a></b><br>
For many random points in an equilateral triangle, the smallest enclosing copy fits inside with probability tending to 13/48, not 1/2.<br>
<sub><a href="smallest-enclosing-copy/paper">paper</a> · <a href="smallest-enclosing-copy/lean">Lean</a> · <a href="smallest-enclosing-copy/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="random-chords-two-circles"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/chords.svg" width="100%" alt="Random lines past three circles"></a>
<p><b><a href="random-chords-two-circles">Random lines past three circles</a></b><br>
Lines AB and BC hit the third circle equally often, for every ratio of radii in geometric progression.<br>
<sub><a href="random-chords-two-circles/paper">paper</a> · <a href="random-chords-two-circles/lean">Lean</a> · <a href="random-chords-two-circles/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="hamiltonian-cubic-graph"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/cubic.svg" width="100%" alt="A cubic graph with no (n−1)-cycle"></a>
<p><b><a href="hamiltonian-cubic-graph">A cubic graph with no (n−1)-cycle</a></b><br>
Hamiltonian, not bipartite, and no cycle of length 19: an answer to Gordon Royle's question.<br>
<sub><a href="hamiltonian-cubic-graph/paper">paper</a> · <a href="hamiltonian-cubic-graph/lean">Lean</a> · <a href="hamiltonian-cubic-graph/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="shuffle-anti-squares"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/necklace.svg" width="100%" alt="Necklaces no cut can split"></a>
<p><b><a href="shuffle-anti-squares">Necklaces no cut can split</a></b><br>
Shuffle anti-squares exist in every even length from 24, as Grytczuk, Pawlik and Pleszczyński conjectured.<br>
<sub><a href="shuffle-anti-squares/paper">paper</a> · <a href="shuffle-anti-squares/lean">Lean</a> · <a href="shuffle-anti-squares/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="mex-sequence-not-periodic"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/mex.svg" width="100%" alt="A mex sequence that never repeats"></a>
<p><b><a href="mex-sequence-not-periodic">A mex sequence that never repeats</a></b><br>
Guy's question E27: the sequence from 1,1,1,0,1,0,1,1 is unbounded, so not ultimately periodic.<br>
<sub><a href="mex-sequence-not-periodic/paper">paper</a> · <a href="mex-sequence-not-periodic/lean">Lean</a> · <a href="mex-sequence-not-periodic/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="hofstadter-conway-comparison"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/conway.svg" width="100%" alt="Newman-Conway and its cousin"></a>
<p><b><a href="hofstadter-conway-comparison">Newman-Conway and its cousin</a></b><br>
Alkan's alternating variant never strays further from n/2 than the Newman-Conway sequence.<br>
<sub><a href="hofstadter-conway-comparison/paper">paper</a> · <a href="hofstadter-conway-comparison/lean">Lean</a> · <a href="hofstadter-conway-comparison/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="polynomial-lemniscates"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/lemniscates.svg" width="100%" alt="Two figures of eight"></a>
<p><b><a href="polynomial-lemniscates">Two figures of eight</a></b><br>
Polynomial lemniscates meet in at most 2n₁n₂ − 2 points; two lemniscates of Bernoulli in at most six.<br>
<sub><a href="polynomial-lemniscates/paper">paper</a> · <a href="polynomial-lemniscates/lean">Lean</a> · <a href="polynomial-lemniscates/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="balanced-ternary-quotients"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/balanced-ternary.svg" width="100%" alt="Quotients of balanced ternary numbers"></a>
<p><b><a href="balanced-ternary-quotients">Quotients of balanced ternary numbers</a></b><br>
Guy's question F31: infinitely many integers are not a ratio of two numbers whose balanced-ternary digits are all 1 or −1.<br>
<sub><a href="balanced-ternary-quotients/paper">paper</a> · <a href="balanced-ternary-quotients/lean">Lean</a> · <a href="balanced-ternary-quotients/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="descent-sets-inverse"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/descent-sets.svg" width="100%" alt="Descent sets of a permutation and its inverse"></a>
<p><b><a href="descent-sets-inverse">Descent sets of a permutation and its inverse</a></b><br>
Almost every pair of subsets occurs, so Stanley's growth rate is L = 4.<br>
<sub><a href="descent-sets-inverse/paper">paper</a> · <a href="descent-sets-inverse/lean">Lean</a> · <a href="descent-sets-inverse/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="alternating-sum-positivity"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/alternating-sum.svg" width="100%" alt="An alternating sum that is never negative"></a>
<p><b><a href="alternating-sum-positivity">An alternating sum that is never negative</a></b><br>
Abdesselam's sum L(u,a,b,n) is nonnegative, and Taylor's and Hucht's conjectures follow.<br>
<sub><a href="alternating-sum-positivity/paper">paper</a> · <a href="alternating-sum-positivity/lean">Lean</a> · <a href="alternating-sum-positivity/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="symmetric-polynomial-ratio"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/symmetric-ratio.svg" width="100%" alt="A ratio of symmetric polynomials"></a>
<p><b><a href="symmetric-polynomial-ratio">A ratio of symmetric polynomials</a></b><br>
Ait-Haddou's ratio of complete homogeneous symmetric polynomials increases, for every degree and position.<br>
<sub><a href="symmetric-polynomial-ratio/paper">paper</a> · <a href="symmetric-polynomial-ratio/lean">Lean</a> · <a href="symmetric-polynomial-ratio/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="even-and-odd-dyck-paths"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/dyck-signs.svg" width="100%" alt="Even and odd Dyck paths"></a>
<p><b><a href="even-and-odd-dyck-paths">Even and odd Dyck paths</a></b><br>
Weight a Dyck path by its valley positions: even minus odd is the number of symmetric paths. Cigler's question, a combinatorial proof.<br>
<sub><a href="even-and-odd-dyck-paths/paper">paper</a> · <a href="even-and-odd-dyck-paths/lean">Lean</a> · <a href="even-and-odd-dyck-paths/verify">code</a></sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="sylow-cycle-polynomials"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/sylow.svg" width="100%" alt="Counting cycles in a Sylow 2-subgroup"></a>
<p><b><a href="sylow-cycle-polynomials">Counting cycles in a Sylow 2-subgroup</a></b><br>
The two factors Stanley observed are irreducible over the rationals at every level.<br>
<sub><a href="sylow-cycle-polynomials/paper">paper</a> · <a href="sylow-cycle-polynomials/lean">Lean</a> · <a href="sylow-cycle-polynomials/verify">code</a></sub></p>
</td>
<td width="50%" valign="top">
<a href="half-window-sequence"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/half-window.svg" width="100%" alt="A sequence that looks back half way"></a>
<p><b><a href="half-window-sequence">A sequence that looks back half way</a></b><br>
If a(n) drops by a(⌊n/2⌋)/n at each odd step, then n a(n) tends to 1/(1 − ln 2), as a commenter guessed from the digits.<br>
<sub><a href="half-window-sequence/paper">paper</a> · <a href="half-window-sequence/lean">Lean</a> · <a href="half-window-sequence/verify">code</a></sub></p>
</td>
</tr>
</table>

### Open problems settled, verified by computation

Proved by exhaustive search with independent cross-checks, or by hand with parts in Lean.

<table>
<tr>
<td width="50%" valign="top">
<a href="equal-perimeter-rectangles"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/equal-perimeter.svg" width="100%" alt="Equal perimeters, no two alike"></a>
<p><b><a href="equal-perimeter-rectangles">Equal perimeters, no two alike</a></b><br>
A square splits into nine rectangles of equal perimeter, no two congruent; nine is the fewest, with exactly five solutions.<br>
<sub><a href="equal-perimeter-rectangles/paper">paper</a> · <a href="equal-perimeter-rectangles/verify">code</a> · Exhaustive search, two independent programs</sub></p>
</td>
<td width="50%" valign="top">
<a href="squared-rectangle-697x611"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/squaring.svg" width="100%" alt="697 × 611 in fourteen squares"></a>
<p><b><a href="squared-rectangle-697x611">697 × 611 in fourteen squares</a></b><br>
The rectangle needs exactly fourteen squares, not seventeen, so it is not a counterexample to the minimal squaring conjecture.<br>
<sub><a href="squared-rectangle-697x611/paper">paper</a> · <a href="squared-rectangle-697x611/verify">code</a> · Complete enumeration, checked against OEIS</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/bishops.svg" width="100%" alt="Three armies of bishops"></a>
<p><b><a href="math-magic-problems">Three armies of bishops</a></b><br>
Three armies of five bishops fit on a 5 × 5 board and three of eight on 6 × 6, and no more: Friedman's two values.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Exhaustive count of diagonal labellings</sub></p>
</td>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/capture.svg" width="100%" alt="Chess capture patterns"></a>
<p><b><a href="math-magic-problems">Chess capture patterns</a></b><br>
Friedman's capture digraphs q, r and s are not made by any chess position, on any board.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Two independent solvers</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/kings.svg" width="100%" alt="Kings that touch in a cycle"></a>
<p><b><a href="math-magic-problems">Kings that touch in a cycle</a></b><br>
Kings with touch counts (1,3,6), (1,6,3) or (2,3,4) admit no finite arrangement: Friedman's unsolved problem 24.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · DRUP certificates, independent Z3 check</sub></p>
</td>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/heptomino.svg" width="100%" alt="A heptomino that never balances"></a>
<p><b><a href="math-magic-problems">A heptomino that never balances</a></b><br>
This heptomino never fills a square with equal row and column counts, in any size: one shape of Friedman's problem 15.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Proof by hand, exact checker</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/tournament.svg" width="100%" alt="A tournament schedule that beats the table"></a>
<p><b><a href="math-magic-problems">A tournament schedule that beats the table</a></b><br>
Friedman's optimal tournaments: exact best schedules over all adaptive plans, two of them better than the published values.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Exact recursion, two programs</sub></p>
</td>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/prime-signature.svg" width="100%" alt="A misfiled prime signature"></a>
<p><b><a href="math-magic-problems">A misfiled prime signature</a></b><br>
In Friedman's prime-signature table, 1022303⁴ belongs in cell (4, 411), where it is the smallest; cell (4, 41) is empty.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Proof by hand, computer search</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="powers-of-four-representations"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/powers-of-four.svg" width="100%" alt="Deleting the powers of four"></a>
<p><b><a href="powers-of-four-representations">Deleting the powers of four</a></b><br>
Remove 16, 64, 256, … and the ordered ways to write n as a sum of three survivors still rise at every n: Sándor and Yang's Remark 1.3.<br>
<sub><a href="powers-of-four-representations/paper">paper</a> · <a href="powers-of-four-representations/lean">Lean</a> · <a href="powers-of-four-representations/verify">code</a> · Proposition 1 in Lean; Problem 1.4 facts by hand</sub></p>
</td>
<td width="50%" valign="top">
<a href="tangent-circles-incentre"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/tangent-circles.svg" width="100%" alt="Three circles and a fair coin"></a>
<p><b><a href="tangent-circles-incentre">Three circles and a fair coin</a></b><br>
A triangle through random points on three touching circles contains the incentre with probability exactly 1/2, for all radii.<br>
<sub><a href="tangent-circles-incentre/paper">paper</a> · <a href="tangent-circles-incentre/lean">Lean</a> · <a href="tangent-circles-incentre/verify">code</a> · Partly in Lean; geometry by hand</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="zero-sum-selection-game"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/zero-sum.svg" width="100%" alt="A zero-sum selection game"></a>
<p><b><a href="zero-sum-selection-game">A zero-sum selection game</a></b><br>
Lev's question: the winning matrices form a union of subspaces of dimension n(n+1)/2 − 1, and recognising them is Π₂ᵖ-complete.<br>
<sub><a href="zero-sum-selection-game/paper">paper</a> · <a href="zero-sum-selection-game/lean">Lean</a> · <a href="zero-sum-selection-game/verify">code</a> · Partly in Lean; reduction by hand</sub></p>
</td>
<td width="50%" valign="top">
<a href="inverse-pairs-five"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/inverse-pairs.svg" width="100%" alt="Five from inverse pairs"></a>
<p><b><a href="inverse-pairs-five">Five from inverse pairs</a></b><br>
Summing 1/√(a·ā) over a and its inverse mod p gives 5 + O(p^(−1/8+ε)): the inverse pairs behave like all pairs, and those sum to (∑ 1/√a)²/p → 4.<br>
<sub><a href="inverse-pairs-five/paper">paper</a> · <a href="inverse-pairs-five/lean">Lean</a> · <a href="inverse-pairs-five/verify">code</a> · In Lean, assuming Weil's bound</sub></p>
</td>
</tr>
</table>

### Partial progress

Part of the question answered; the rest is still open.

<table>
<tr>
<td width="50%" valign="top">
<a href="latin-squares-small-rank"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/latin-rank.svg" width="100%" alt="Latin squares of small rank"></a>
<p><b><a href="latin-squares-small-rank">Latin squares of small rank</a></b><br>
Every Latin square of order n has rank at least 1 + 3(n−1)/(n+1), so at least 4 from n = 5 on; the least ranks up to order 8 are 1, 2, 3, 3, 5, 4, 6, 4.<br>
<sub><a href="latin-squares-small-rank/paper">paper</a> · <a href="latin-squares-small-rank/lean">Lean</a> · <a href="latin-squares-small-rank/verify">code</a> · Bound and r(6), r(8) in Lean; r(5), r(7) by exact search</sub></p>
</td>
<td width="50%" valign="top">
<a href="good-permutations-mersenne"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/good-perm.svg" width="100%" alt="Permutations with no whole-number averages"></a>
<p><b><a href="good-permutations-mersenne">Permutations with no whole-number averages</a></b><br>
If no proper block of a permutation of 1..n averages to a whole number, then n = 2ᵐ − 1; the asker's example works exactly when n is prime, and n = 15, 63 have none.<br>
<sub><a href="good-permutations-mersenne/paper">paper</a> · <a href="good-permutations-mersenne/lean">Lean</a> · <a href="good-permutations-mersenne/verify">code</a> · Theorems in Lean; n ≤ 63 by two searches</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="catching-the-centroid"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/centroid-circle.svg" width="100%" alt="Catching the centroid"></a>
<p><b><a href="catching-the-centroid">Catching the centroid</a></b><br>
A circle on a random diameter of a convex region contains the centroid with probability at most 14/27 ≈ 0.5185; the equilateral triangle's 0.5164 is conjectured best.<br>
<sub><a href="catching-the-centroid/paper">paper</a> · <a href="catching-the-centroid/lean">Lean</a> · <a href="catching-the-centroid/verify">code</a> · Bounds in Lean; sharp value open</sub></p>
</td>
<td width="50%" valign="top">
<a href="broken-stick-feynman"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/broken-stick.svg" width="100%" alt="A broken stick and a Feynman diagram"></a>
<p><b><a href="broken-stick-feynman">A broken stick and a Feynman diagram</a></b><br>
The chance that six random pieces of a stick make a tetrahedron is a three-loop Feynman diagram; it is 0.0125749944…, not 1/79.<br>
<sub><a href="broken-stick-feynman/paper">paper</a> · <a href="broken-stick-feynman/lean">Lean</a> · <a href="broken-stick-feynman/verify">code</a> · Algebra in Lean; no closed form</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="prime-squares-half-turns"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/prime-squares.svg" width="100%" alt="Prime squares and half-turns"></a>
<p><b><a href="prime-squares-half-turns">Prime squares and half-turns</a></b><br>
A p × p square, p prime, cut into p congruent pieces that are only translated or half-turned must be cut into bars; with quarter-turns too, the question is open.<br>
<sub><a href="prime-squares-half-turns/paper">paper</a> · <a href="prime-squares-half-turns/lean">Lean</a> · <a href="prime-squares-half-turns/verify">code</a> · Algebra in Lean; full question open</sub></p>
</td>
<td width="50%" valign="top">
<a href="five-numbers-many-averages"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/five-numbers.svg" width="100%" alt="Five numbers, many averages"></a>
<p><b><a href="five-numbers-many-averages">Five numbers, many averages</a></b><br>
Replacing two numbers by their average, the five integers (5N, 0, 4N, 3N±5, 3N±5) with N = 2ᵏ⁺¹ need exactly k + 3 moves to become equal, so five numbers have no bound on the shortest solution.<br>
<sub><a href="five-numbers-many-averages/paper">paper</a> · <a href="five-numbers-many-averages/lean">Lean</a> · <a href="five-numbers-many-averages/verify">code</a> · In Lean; which lists are solvable is open</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="why-the-sphere-beats-the-ball"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/sphere-ball.svg" width="100%" alt="Why the sphere beats the ball"></a>
<p><b><a href="why-the-sphere-beats-the-ball">Why the sphere beats the ball</a></b><br>
Three points on concentric spheres form an acute triangle with probability at most 1/2, equal only when the two outer radii agree; so the uniform sphere beats every rotationally invariant law in space, while in the plane moving mass inwards helps.<br>
<sub><a href="why-the-sphere-beats-the-ball/paper">paper</a> · <a href="why-the-sphere-beats-the-ball/lean">Lean</a> · <a href="why-the-sphere-beats-the-ball/verify">code</a> · Formula and bound in Lean; the disc's gain unexplained</sub></p>
</td>
<td width="50%" valign="top">
<a href="raising-the-apex"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/raising-apex.svg" width="100%" alt="Raising the apex raises the Gaussian centroid"></a>
<p><b><a href="raising-the-apex">Raising the apex raises the Gaussian centroid</a></b><br>
Raise a triangle's apex along the perpendicular through a point of its base and the Gaussian centre of mass rises, in every dimension and wherever the Gaussian is centred; whether it always pins down the moving vertex is open.<br>
<sub><a href="raising-the-apex/paper">paper</a> · <a href="raising-the-apex/lean">Lean</a> · <a href="raising-the-apex/verify">code</a> · Steps after Prékopa's theorem in Lean; oblique case open</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="sixteen-words"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/sixteen-words.svg" width="100%" alt="Sixteen words cover all 15-bit strings"></a>
<p><b><a href="sixteen-words">Sixteen words cover all 15-bit strings</a></b><br>
Deleting five bits from every 15-bit string can leave just 16 different strings, down from 17 in 2013, so the growth rate of the n/3-deletion problem is at most 16^(1/15) < 1.2031; among symmetric sets 16 is optimal.<br>
<sub><a href="sixteen-words/paper">paper</a> · <a href="sixteen-words/lean">Lean</a> · <a href="sixteen-words/verify">code</a> · Rate argument in Lean; cover and optimality by certified computation</sub></p>
</td>
<td width="50%" valign="top">
<a href="unit-hexagon-diameter"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/hexagon.svg" width="100%" alt="Six matchsticks in a square"></a>
<p><b><a href="unit-hexagon-diameter">Six matchsticks in a square</a></b><br>
No simple loop of six unit sticks fits in a unit square: the six-stick case of an open parity question.<br>
<sub><a href="unit-hexagon-diameter/paper">paper</a> · <a href="unit-hexagon-diameter/lean">Lean</a> · <a href="unit-hexagon-diameter/verify">code</a> · Partly in Lean</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="randomized-pascal-triangle"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/pascal.svg" width="100%" alt="A randomized Pascal triangle"></a>
<p><b><a href="randomized-pascal-triangle">A randomized Pascal triangle</a></b><br>
The expected average blows up whenever p ≥ 0.232; whether it does for every p > 0 is open.<br>
<sub><a href="randomized-pascal-triangle/paper">paper</a> · <a href="randomized-pascal-triangle/lean">Lean</a> · <a href="randomized-pascal-triangle/verify">code</a> · In Lean</sub></p>
</td>
<td width="50%" valign="top">
<a href="power-two-tree-labels"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/power-two-tree.svg" width="100%" alt="Labelling binary trees by powers of two"></a>
<p><b><a href="power-two-tree-labels">Labelling binary trees by powers of two</a></b><br>
Every tree with at most 24 vertices can be labelled 0 to n − 1 with power-of-two steps; five constructions and an exact rule for universal label sets narrow any counterexample.<br>
<sub><a href="power-two-tree-labels/paper">paper</a> · <a href="power-two-tree-labels/lean">Lean</a> · <a href="power-two-tree-labels/verify">code</a> · Constructions and lemmas in Lean; searches by two programs</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="wandering-over-divisors"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/divisor-walk.svg" width="100%" alt="Wandering over the divisors of 10ⁿ"></a>
<p><b><a href="wandering-over-divisors">Wandering over the divisors of 10ⁿ</a></b><br>
Players multiply by 2 or 5 or divide by 10, never repeating a divisor. The tournament's natural answer fails from 10⁶ on, and the second player beats whole families of openings on every board.<br>
<sub><a href="wandering-over-divisors/paper">paper</a> · <a href="wandering-over-divisors/lean">Lean</a> · <a href="wandering-over-divisors/verify">code</a> · Theorems in Lean; tables by two programs</sub></p>
</td>
<td width="50%" valign="top">
<a href="https://github.com/jvvk/taxicab-distances-eleven"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/taxicab.svg" width="100%" alt="Eleven points, distances 1 to 55"></a>
<p><b><a href="https://github.com/jvvk/taxicab-distances-eleven">Eleven points, distances 1 to 55</a></b><br>
Eleven lattice points whose 55 taxicab distances are exactly 1 to 55: the case n = 11 of an open question.<br>
<sub><a href="https://github.com/jvvk/taxicab-distances-eleven">repository</a> · Computer search</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="cube-unfoldings-tile-space"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/cube-unfoldings.svg" width="100%" alt="Unfolded cubes that tile space"></a>
<p><b><a href="cube-unfoldings-tile-space">Unfolded cubes that tile space</a></b><br>
Every one of the 502,110 unfoldings of the six-dimensional cube tiles five-space with its point reflection, extending Firet's five-cube result.<br>
<sub><a href="cube-unfoldings-tile-space/paper">paper</a> · <a href="cube-unfoldings-tile-space/lean">Lean</a> · <a href="cube-unfoldings-tile-space/verify">code</a> · Certificates, two checkers; lemmas in Lean</sub></p>
</td>
<td width="50%" valign="top">
<a href="balanced-tree-agreement-subtrees"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/balanced-mast.svg" width="100%" alt="How much two balanced trees must share"></a>
<p><b><a href="balanced-tree-agreement-subtrees">How much two balanced trees must share</a></b><br>
Two balanced trees on n leaves always agree on at least n^0.243 leaves, and some on only n^(5/11); Martin and Thatte conjectured n^(1/2).<br>
<sub><a href="balanced-tree-agreement-subtrees/paper">paper</a> · <a href="balanced-tree-agreement-subtrees/lean">Lean</a> · <a href="balanced-tree-agreement-subtrees/verify">code</a> · Lean, except one certified inequality</sub></p>
</td>
</tr>
<tr>
<td width="50%" valign="top">
<a href="math-magic-problems"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/slabs.svg" width="100%" alt="Cubes cut into slabs"></a>
<p><b><a href="math-magic-problems">Cubes cut into slabs</a></b><br>
A cube made of one k-slab for each k ≤ n has side at most n(n+1)/2, and none exists for n = 4, 5, 6; Friedman conjectures infinitely many.<br>
<sub><a href="math-magic-problems/paper">paper</a> · <a href="math-magic-problems/verify">code</a> · Bound by hand, n = 4 to 6 by two searches</sub></p>
</td>
<td width="50%" valign="top">
<a href="span-maximising-chains"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/chains.svg" width="100%" alt="The chain that reaches farthest"></a>
<p><b><a href="span-maximising-chains">The chain that reaches farthest</a></b><br>
Every best chain has lengths rising then falling; exactly three orders occur for four segments, and the general count is open.<br>
<sub><a href="span-maximising-chains/paper">paper</a> · <a href="span-maximising-chains/lean">Lean</a> · <a href="span-maximising-chains/verify">code</a> · Shape theorem in Lean</sub></p>
</td>
</tr>
</table>

### New proofs of known results

<table>
<tr>
<td width="50%" valign="top">
<a href="six-circles-rectangle"><img src="https://raw.githubusercontent.com/jvvk/jvvk/565921e624a6354d08574448f905c63736ebd049/assets/six-circles.svg" width="100%" alt="Six circles in a rectangle"></a>
<p><b><a href="six-circles-rectangle">Six circles in a rectangle</a></b><br>
The red segment is exactly as long as the rectangle is tall: a proof by classical geometry alone.<br>
<sub><a href="six-circles-rectangle/paper">paper</a> · <a href="six-circles-rectangle/lean">Lean</a> · <a href="six-circles-rectangle/verify">code</a> · In Lean, step by step</sub></p>
</td>
<td width="50%"></td>
</tr>
</table>

## Details

Every paper, its status and exactly what was checked, and how.
<!-- visual:end -->

| Result | Kind | Status | Verified |
|---|---|---|---|
| [Sixteen words cover all 15-bit strings](sixteen-words/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (H(15,5) ≤ 16 improves 17; the rate α is open) | Lean (block lemma, H submultiplicative, Fekete limit via Mathlib, α ≤ 16^(1/15) from a 16-word cover, numerical bounds; standard axioms only); the cover checked by two independent programs; symmetric optimum by two solvers and a drat-trim-verified DRAT proof |
| [Raising the apex raises the Gaussian centroid](raising-the-apex/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (oblique and general nested cases open) | Lean (cone lemma, increments of concave increasing functions, monotone likelihood ratio, Chebyshev's integral inequality and its strict form, mean comparison; standard axioms only); Prékopa's theorem and the Gaussian factorisation quoted; every stated number asserted; independent Monte Carlo recheck including a tetrahedron |
| [Why the sphere beats the ball](why-the-sphere-beats-the-ball/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (the disc's gain unexplained) | Lean (obtuse condition, uniform tail, the three cap integrals for every a ≥ b ≥ c > 0, the formula, P ≤ 1/2 with equality iff a = b, one-centre case, the mixture polynomials; standard axioms only); hat-box theorem and conditioning quoted; cap integrals by quadrature for 43 triples; independent simulation and exact ball integral |
| [Five numbers, many averages](five-numbers-many-averages/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (which lists are solvable is open) | Lean (every step: dyadic weights, affine invariance, the first-hit divisibility, the count of entries at the mean, lower bound for every strategy, explicit k + 3 strategy for every k, integer form, no balanced subset; standard axioms only); every stated number asserted, least moves for k ≤ 6 by complete search; independent integer recheck |
| [Prime squares and half-turns](prime-squares-half-turns/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (quarter-turns and several reflections open) | Lean (the orientation argument in any UFD with an involution and an evaluation, the row and bar lemmas in Z[x][y], Q_p irreducible with Q_p(1) = p; standard axioms only); unique factorisation of the Laurent ring and the tiling identity quoted; exhaustive search n ≤ 14 with every quoted number asserted; independent recheck of all p-cell sets for p = 3, 5 and all heptominoes |
| [A broken stick and a Feynman diagram](broken-stick-feynman/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (no closed form) | Lean (the algebra of Theorem 1 for the triangle and the tetrahedron: Gram map and its determinant, trace identity, 16 spanning trees, matrix-tree, duality, substitution, constants, p_2 = 1/4; standard axioms only); analytic inputs quoted; p_3 by two independent quadratures to 10^-12, Theorem 1 by Monte Carlo for n = 2, 3, 4, every number asserted, independent recheck |
| [Catching the centroid](catching-the-centroid/) | Note | Preprint, 10 October 2026; not peer reviewed; partial progress (sharp conjecture open) | Lean (Propositions 1–3, the signed-area formula, Lemma 1, Theorem 1 and the 8/15 bound for continuous periodic angular densities; standard axioms only); Grünbaum, Stewart and Minkowski–Radon inequalities quoted as hypotheses; exact polygon evaluators, all numerical claims asserted, independent recheck |
| [A sequence that looks back half way](half-window-sequence/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (every step: the window identity, the window weights tend to ln 2, boundedness, the contraction, n a(n) → 1/(1 − ln 2); standard axioms only); exact checks with three false variants; the rate numerical only |
| [Latin squares of small rank](latin-squares-small-rank/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (the lower bound 1 + 3(n−1)/(n+1) and its strict form for odd n, r(n) ≥ 4 for n ≥ 5, r(4) = 3, r(6) = 4, r(8) = 4; standard axioms only); r(5) = 5 and r(7) = 6 by an exhaustive computation with an exact modular certificate, with a false variant |
| [Permutations with no whole-number averages](good-permutations-mersenne/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (Bîsceanu's theorem that good forces n = 2^m − 1, with te4's 2-adic congruence; the search reduction; the asker's permutation good iff n is prime; standard axioms only); exhaustive searches n = 7, 15, 31, 63 by two C programs, with a planted error caught |
| [Five from inverse pairs](inverse-pairs-five/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (every step: rectangles via Fourier analysis, staircase, divisor bound, layer-cake identity, full-grid limit, the rate p^(−1/8+ε) and S(p) → 5; Weil's bound for Kloosterman sums as an explicit hypothesis, not an axiom; standard axioms only); independent C and Python computations with planted errors caught |
| [Labelling binary trees by powers of two](power-two-tree-labels/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (Theorem 1 (a)-(e): unary root, parity incl. sizes differing by one, Mersenne, one- and two-prefix constructions; tail and primitive-tail lemmas; span bound; standard axioms only); all trees n ≤ 24 by one program (two to 22), root condition n ≤ 22, universal sets n ≤ 21 (two programs to 20); independent Python recheck to n = 12 |
| [Wandering over the divisors of a power of ten](wandering-over-divisors/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (Lemma 2 and Theorems 3, 5, 7 for every board size: edge sweep, diagonal climb, bottom row, corners, (2,0), (2,2); standard axioms only); Theorem 1 and every table by two independent exhaustive solvers (C and Python) up to 9 × 9, C to 10 × 10 |
| [Even and odd Dyck paths](even-and-odd-dyck-paths/) | Note | Preprint, 10 October 2026; not peer reviewed | Lean (Dyck paths as step lists, valley encoding, partner involution, fixed-word sign, halving and last departures, Theorem 1; standard axioms only); Fürlinger–Hofbauer identity quoted, checked for n ≤ 8; independent recheck |
| [Deleting the powers of four: strictly increasing representation functions](powers-of-four-representations/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (the coefficient bound, the reduction to three summands, the count of ordered triples, Proposition 1; standard axioms only); Propositions 4 and 5 by hand; direct convolution and an identity check to 10^6, with a false variant |
| [Every unfolding of the six-dimensional cube tiles five-space](cube-unfoldings-tile-space/) | Paper | Preprint, 9 October 2026; not peer reviewed | Lean (the quotient lemmas and the worked five-cube example; standard axioms only); the 9,694 and 502,110 tiling certificates by independent checkers sharing no code with the searches, not in Lean |
| [Seven problems from Erich Friedman's *Math Magic*](math-magic-problems/) | Paper | Preprint v2, 9 October 2026; not peer reviewed | Armies of bishops by an exhaustive count of diagonal labellings; touch cycles by DRUP certificates and an independent Z3 encoding; capture digraphs by two independent solver models (Z3, cvc5) and a simulator; the heptomino and the slab-cube bound by hand, with exact checkers; slab cubes for n = 4, 5, 6 by a solver and an independent solver-free search; prime signatures by exact computation; tournaments by two exact programs. No Lean |
| [Agreement subtrees of balanced trees: the exponent lies between 0.243 and 5/11](balanced-tree-agreement-subtrees/) | Paper | Preprint, 9 October 2026; not peer reviewed | Lean (substitution lemma and existence of the exponent, β ≤ 5/11 with an explicit 2048-leaf pair, M(n) ≥ n^0.235 including its certificate, the two-level induction; standard axioms only); the inequality behind n^0.243 by an exact-arithmetic certifier, not in Lean |
| [A zero-sum selection game on matrices](zero-sum-selection-game/) | Paper | Preprint, 9 October 2026; not peer reviewed | Lean (rank lemma and dimension theorem for all row lengths and quotas, order-three criterion and distinct-entry classification, two-valued normal form; standard axioms only); 3 × 3 components and the reduction by an independent checker |
| [Random chords of two circles and a third centre](random-chords-two-circles/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every proved result: Lemmas 1 to 3, Theorem 4, Corollaries 5 to 8, the remarks; standard axioms only); exact and numerical checkers with false variants |
| [A comparison theorem for the Hofstadter–Conway $10,000 sequence and its alternating variant](hofstadter-conway-comparison/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorem 1, every lemma, Proposition 4.1 and Corollary 4.2; standard axioms only); every printed number and the lemmas on all symmetric words to length 34 by an independent checker |
| [Positivity of an alternating sum from random overlaps in C^N](alternating-sum-positivity/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorem 1, every corollary, Taylor's formula and Hucht's identity; standard axioms only); every identity by an exact checker |
| [Polynomial lemniscates meet in at most 2n₁n₂ − 2 points](polynomial-lemniscates/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorem 1, Corollaries 2 and 3 and every lemma; standard axioms only); the ten points of the (2,3) example by interval arithmetic and an independent program |
| [Descent sets of a permutation and its inverse: almost every pair occurs](descent-sets-inverse/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every proved result: Theorems 1.1, 1.2 and 3.6, Lemma 2.1 both ways, Lemma 3.5, Corollary 3.7); every stated number by independent programs |
| [Does the smallest enclosing copy fit? Random points in a convex polygon](smallest-enclosing-copy/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every theorem, lemma and corollary); numerical values by independent programs |
| [A mex sequence that is not ultimately periodic](mex-sequence-not-periodic/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (every lemma and theorem, by two routes); every quoted number by an exact checker |
| [Infinitely many integers that are not quotients of zero-free balanced ternary numbers](balanced-ternary-quotients/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorems 1.1 and 1.3; generated proofs, core Lean); every quoted number by an exact checker; independent symbolic checker for Theorem 1.1 |
| [Tiling almost-squares with smaller distinct almost-squares](almost-square-tilings/) | Paper | Preprint, 8 October 2026; not peer reviewed | Independent checker for every finite case; Lean (Theorem 1, every lemma and printed number; n = 16, 17, 19 by `native_decide`) |
| [Two triangulations that share only their hull](two-triangulations-hull/) | Paper | Preprint, 8 October 2026 | Exact checker; exhaustive order-type search to n = 10; Lean (Theorem 2 assumes the n = 6 to 8 search) |
| [Shuffle anti-squares of every even length from 24](shuffle-anti-squares/) | Paper | Preprint, 8 October 2026 | Lean (Theorems 2 and 4, Corollary 6, all examples); exhaustive searches each confirmed by a second, independent program |
| [Which orders maximise the span of a chain?](span-maximising-chains/) | Paper | Preprint, 8 October 2026; not peer reviewed | Lean (Theorem 1 and a₄ = 3; standard axioms only); realisation theorem and every witness by exact programs, two written independently |
| [Monotonicity of a ratio of complete homogeneous symmetric polynomials](symmetric-polynomial-ratio/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (Theorem 1 and the lemmas of its proof; standard axioms only); every identity in exact arithmetic by an independent checker |
| [A Hamiltonian cubic graph with no cycle of length n − 1](hamiltonian-cubic-graph/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (every statement for the 20-vertex graph; the cycle theorem by the counting argument; standard axioms only); exhaustive cycle search by an independent program |
| [The 697 × 611 rectangle needs exactly fourteen squares](squared-rectangle-697x611/) | Note | Preprint, 9 October 2026; not peer reviewed | Tiling checked cell by cell; lower bound by complete enumeration of squared rectangles with at most 13 squares, which reproduces every value of OEIS A219158 up to 14 (65,231 rectangles) and catches a mutant. No Lean |
| [A randomized Pascal triangle whose average blows up](randomized-pascal-triangle/) | Note | Preprint v2, 9 October 2026; not peer reviewed | Lean (Theorems 1 and 2 and L_p = ∞ for p ≥ 29/125, including the certificate's local inequality checked region by region; standard axioms only); certificate also checked by two independent programs |
| [Six unit sticks and the diameter of a hexagon](unit-hexagon-diameter/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (lemmas, triangle proposition, counting, sign lemmas, sharpness family; standard axioms only); pocket topology by hand; independent recheck |
| [Counting cycles in a Sylow 2-subgroup](sylow-cycle-polynomials/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (the composition lemma, both factorizations, coefficient agreement, irreducibility over Q for every n; standard axioms only); cycle counts by listing the group for n ≤ 4; independent recheck |
| [Three tangent circles and a fair coin](tangent-circles-incentre/) | Note | Preprint, 9 October 2026; not peer reviewed | Lean (chord identities, the integral π, crossing law, final sum, sphere folding; standard axioms only); change of variables and plane geometry by hand; independent recheck |
| [Six circles in a rectangle: a proof by pure geometry](six-circles-rectangle/) | Note | Preprint, 8 October 2026 | Every step checked numerically to 50 digits; Lean, step by step |
| [Nine rectangles of equal perimeter, no two alike, in a square](equal-perimeter-rectangles/) | Note | Preprint, 8 October 2026 | Exact rational enumeration of every type to n = 9 by two independent programs; counts match OEIS A100664 |

Papers and figures are released under [CC BY 4.0](LICENSE-PAPERS), code under the [MIT licence](LICENSE-CODE).
