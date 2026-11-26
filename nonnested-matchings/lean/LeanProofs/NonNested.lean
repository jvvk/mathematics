import LeanProofs.NonNested.Defs
import LeanProofs.NonNested.Short
import LeanProofs.NonNested.Fence
import LeanProofs.NonNested.K3
import LeanProofs.NonNested.K4
import LeanProofs.NonNested.K4Plain
import LeanProofs.NonNested.Report

/-
# Non-nested matchings in ordered graphs: the cases k = 3 and k = 4

Formalises the note `nonnested.tex` (`cc33-nonnested-1-1/note/`) (namespace `NonNested`),
on Barát, Freschi and Tóth, Conjecture 2.6 (arXiv:2512.15461).

Formalised:
* `short_le_eight`, `short_eq_eight`: Lemma 3 (at most 8 short edges; exactly 8 only as the
  short stars at `a < b`, `b - a ≥ 3`).
* `fence_L`, `fence_R`: Lemma 4.
* `f3_upper`: a graph on `[n]`, `n ≥ 6`, with no strongly non-nested 3-matching has at most
  `2n` edges.
* `lowerGraph`, `card_lowerGraph`, `noNN_lowerGraph`: the graph with `2n` edges and no
  non-nested 3-matching.
* `theorem1`: Theorem 1, `f_3(n) = f*_3(n) = 2n` for `n ≥ 6` (`IsExtremal` for `NoNN 3` and
  `NoSNN 3`).
* `G9`, `card_G9`, `noSNN4_G9`: the graph on `[9]` with 28 edges and no strongly non-nested
  4-matching.
* `noSNN4_addVertex`, `theorem2`, `strong_conjecture_fails`: Theorem 2, `f*_4(n) ≥ 3n + 1`
  for `n ≥ 9`.
* `K4Plain` (version 2, the plain case `k = 4`): the local star lemmas `lemmaE`, `endWindowA`,
  `endWindowB`, `lemmaM`, `closePair1`, `closePair2`, `exceptional` (each: prescribed edges near a
  vertex plus the long chords of one `3`-star force a non-nested `4`-matching) and the counting
  step `card_le_two_mul`. The rest of the `k = 4` proof (the short-edge classification, the
  star-identification argument and the two finite checks) is not formalised in this version.

Hypotheses, not formalised: `CPHyp` (Capoyleas and Pach, JCTB 56 (1992): at most `4n - 10`
chords with no three pairwise crossing) and `PSHyp` (Pilaud and Santos, DCG 41 (2009),
Corollary 4.2(ii), case k = 2: the 2-star on the inner side of a chord of cyclic length 2).
Both are arguments of `f3_upper` and `theorem1`; Theorem 2 uses neither.
-/
