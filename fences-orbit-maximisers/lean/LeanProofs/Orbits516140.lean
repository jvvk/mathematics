import LeanProofs.Orbits516140.Basic
import LeanProofs.Orbits516140.Count
import LeanProofs.Orbits516140.Aut
import LeanProofs.Orbits516140.Posets
import LeanProofs.Orbits516140.Fences
import LeanProofs.Orbits516140.Report

/-!
# Orbits of linear extensions (MO 516140, answer 516154)

Formalisation of the finite statements in the posted answer to Stanley's question on
`f(P) = e(P)/#Aut(P)`.

* `Orbits516140.Basic`: `LinExt`, the action of `α ≃o α`, `smul_eq_self_iff` (free),
  `card_linExt_eq` (`e = #Aut · f`), `card_aut_dvd`, `orbitCount_eq_div`.
* `Orbits516140.Count`: `cnt` (removal of minimal elements) and `card_linExt_eq_cnt`, proved
  against the definition through `ListExt`.
* `Orbits516140.Aut`: `card_below_map`, `refine`, `card_aut_eq` (a finite candidate check for
  `#Aut`), `IsFenceUnion`, `card_comp_le_two`, `isEmpty_iso_dual`.
* `Orbits516140.Posets`: `Q`, `Q + •`, `R`, `Z₂ + Z₄ + 2•`, `Z₂ + Z₄ + •`, `Z₄`, `Z₆`;
  `e_Q = 298`, `e_R = 1613`, `aut_Q = aut_R = 1`, `R_selfDual`, `Q_not_selfDual`,
  `orbits_Q1 = 2384`, `orbits_F = 2100`, `orbits_F_lt_Q1`, `Q1_not_fenceUnion`.
* `Orbits516140.Fences`: for `n ≥ 181` no `n`-element disjoint union of fences attains `g(n)`
  (`fence_union_not_max`): matching bound `2^t · e ≤ n!` (`two_pow_mul_card_linExt_le`), isolated
  points `k! ≤ #Aut` (`factorial_le_card_aut`), fences have `n ≤ 3t + k` (`exists_matching`),
  Graham's poset with `f ≥ (n - j)!` for `1 ≤ n - j ≤ 2^j` (`exists_poset_orbitCount_ge'`), and
  the arithmetic `n! < (n - J n)! · 2^t · k!` (`factorial_lt`).
* `Orbits516140.Report`: `#print axioms` for the headline results.

The exhaustive search over all posets with at most 11 elements (the column `g(n)` and the
lists of maximisers) stays computational: `~/writing/sources/mo-516140/orbits.c` and the
independent Sage recomputation `sage_g8.sage` for `n ≤ 8`.
-/
