import LeanProofs.ShuffleW.Cut00
import LeanProofs.ShuffleW.Cut01
import LeanProofs.ShuffleW.Cut02
import LeanProofs.ShuffleW.Cut03
import LeanProofs.ShuffleW.Cut04
import LeanProofs.ShuffleW.Cut05
import LeanProofs.ShuffleW.Cut06
import LeanProofs.ShuffleW.Cut07
import LeanProofs.ShuffleW.Cut08
import LeanProofs.ShuffleW.Cut09
import LeanProofs.ShuffleW.Cut10
import LeanProofs.ShuffleW.Cut11
import LeanProofs.ShuffleW.Cut12
import Mathlib.Tactic.IntervalCases

/-!
  Shuffle anti-squares of every even length ≥ 24.

  `W k = 0^(k+5) 1 0^2 1^4 0^(k+4) 1^3 0 1^4` has length 2k + 24, twelve 1s and 2k + 12 zeros, and no
  rotation of it is a shuffle square (one theorem per cut position, files `ShuffleW/CutNN.lean`).
  This settles Conjecture 1 of Grytczuk, Pawlik and Pleszczyński, "Variations on shuffle squares"
  (arXiv 2308.13882v2): for every n ≥ 12 there is a shuffle anti-square of length 2n.
-/

/-- An even binary word none of whose rotations `s ++ p` (where `p ++ s = w`) is a shuffle square. -/
def IsAntiSquare (w : List Bool) : Prop :=
  w.count true % 2 = 0 ∧ w.count false % 2 = 0 ∧
    ∀ p s : List Bool, p ++ s = w → ¬ IsShuffleSquare (s ++ p)

theorem W_rotation_not_square (k : Nat) (p s : List Bool) (h : p ++ s = W k) :
    ¬ IsShuffleSquare (s ++ p) := by
  obtain ⟨P, x, y, S, hp, _, hps⟩ := zruns_append p s
  have hl : (zruns p).length = P.length + 1 := by simp [hp]
  have h13 := congrArg List.length hps
  rw [h, W, zruns_ofGaps] at h13
  simp only [List.length_cons, List.length_nil, List.length_append] at h13
  generalize hn : P.length = n at hl h13
  have : n ≤ 12 := by omega
  interval_cases n
  · exact W_cut00 k p s h (by omega)
  · exact W_cut01 k p s h (by omega)
  · exact W_cut02 k p s h (by omega)
  · exact W_cut03 k p s h (by omega)
  · exact W_cut04 k p s h (by omega)
  · exact W_cut05 k p s h (by omega)
  · exact W_cut06 k p s h (by omega)
  · exact W_cut07 k p s h (by omega)
  · exact W_cut08 k p s h (by omega)
  · exact W_cut09 k p s h (by omega)
  · exact W_cut10 k p s h (by omega)
  · exact W_cut11 k p s h (by omega)
  · exact W_cut12 k p s h (by omega)

theorem W_length (k : Nat) : (W k).length = 2 * k + 24 := by
  simp [W, ofGaps]; omega

theorem W_count_true (k : Nat) : (W k).count true = 12 := by
  simp [W, ofGaps, List.count_append, List.count_replicate]

theorem W_count_false (k : Nat) : (W k).count false = 2 * k + 12 := by
  simp [W, ofGaps, List.count_append, List.count_replicate]; omega

theorem W_isAntiSquare (k : Nat) : IsAntiSquare (W k) :=
  ⟨by rw [W_count_true], by rw [W_count_false]; omega, W_rotation_not_square k⟩

/-- **Main theorem.** For every n ≥ 12 there is a binary shuffle anti-square of length 2n. -/
theorem exists_antiSquare (n : Nat) (hn : 12 ≤ n) :
    ∃ w : List Bool, w.length = 2 * n ∧ IsAntiSquare w :=
  ⟨W (n - 12), by rw [W_length]; omega, W_isAntiSquare _⟩

#print axioms exists_antiSquare
