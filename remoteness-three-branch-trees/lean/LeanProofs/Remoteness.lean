import LeanProofs.Remoteness.Obstruction
import LeanProofs.Remoteness.Family
import LeanProofs.Remoteness.Dist
import LeanProofs.Remoteness.Caterpillar
import LeanProofs.Remoteness.Transmission
import LeanProofs.Remoteness.Headline
import LeanProofs.Remoteness.Degree
import LeanProofs.Remoteness.Prune

/-!
# Remoteness minimisers with three branch vertices (counterexample to Allie et al., Conjecture 4.4)

Tier 1 (model level) of the note's formalisation; plan in
`~/writing/sources/allie-remoteness-segment/lean/PLAN.md`.

* `Remoteness.Obstruction`: Lemma 3.2 (`obstruction`: every splitting of `D'` has two-branch value at least 3892,
  by the note's argument), `attained`, Lemma 3.1 arithmetic (`leafValues`), `T_beats_brooms`.
* `Remoteness.Family`: Lemma 4.3 (`three_branch_loses`) for all `L ≥ p ≥ h ≥ 1`, `a, c ≥ 2`, `b ≥ 1`, with the
  identity `X_add_Z` and the rounding argument.

* `Remoteness.Dist`: `dist_eq_of_local` (a closed form is the graph distance if it is 0 on the diagonal,
  1-Lipschitz along edges, and every vertex has a neighbour one step closer).
* `Remoteness.Caterpillar`: spine-with-arms trees `Cat` (all trees of the headline), `Cat.dist_eq`.
* `Remoteness.Transmission`: `two_trans_leaf` (Lemma 2.1 for caterpillars: closed form at every leaf);
  `trans_spine_le`, `trans_armL_le`, `trans_armR_le` (Lemma 2.2 for caterpillars: along the path between two
  leaves every vertex has transmission at most the larger leaf's, by convexity).
* `Remoteness.Headline`: `headline`: every vertex of `T` has transmission at most 5962 (attained), and every
  starlike or two-branch caterpillar with segment sequence `D` has a vertex of transmission at least 5971.

* `Remoteness.Degree`: degree formulas for caterpillars (`degree_spine`, `degree_arm`); `T_branch` (`T` has exactly
  three branch vertices, spine `0`, `53`, `76`), `Starlike.branch` (exactly one), `TwoHub.branch` (exactly two).
* `Remoteness.Prune`: Lemma 4.2 (`prune`) on the reduced tree (segments contracted to edges, no vertex of degree 2):
  if at most two segments have length other than `h` and some non-pendant segment has length `h`, some non-pendant
  segment of length `h` is adjacent to a pendant segment.

Cited, not formalised: Lemma 4.1 (starring, Allie et al. Lemma 4.1). Not formalised: segment decomposition of an
arbitrary `SimpleGraph` tree (so that every tree with one or two branch vertices is a `Starlike`/`TwoHub`
caterpillar, which is how Allie et al. define these classes) and the 4- and 5-branch rows of Proposition 3.3
(a 4.6-million-case enumeration, checked by two independent programs).
-/
