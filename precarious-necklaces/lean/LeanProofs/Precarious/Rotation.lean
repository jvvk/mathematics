import LeanProofs.Precarious.Basic

/-!
# Precarious necklaces (MO 515996): necklaces and powers

A necklace is a word up to rotation; it is *rotationally symmetric* when some rotation by `0 < s < |w|` fixes
a representative `w`. This file proves that this is the same as `Symm w` (`w` is a proper power), and that it
does not depend on the representative, nor does deleting colours (a rotation of `w` filters to a rotation of
the filtered word). So every theorem stated with `Symm` and `List.filter` is a theorem about necklaces.

* `symm_iff_rotate`: for `w ≠ []`, `Symm w ↔ ∃ s, 0 < s ∧ s < |w| ∧ w.rotate s = w`. If rotation by `s`
  fixes `w`, so does rotation by `d = gcd(s, |w|)` (a multiple of `s` is `d` mod `|w|`), and then `w` has
  period `d`, a divisor of `|w|` below `|w|`.
* `symm_rotate`, `filter_rotate`: representative independence.
-/

set_option linter.unusedSectionVars false

namespace Precarious

open List

variable {α : Type*} [DecidableEq α]

lemma rotate_mul_self {w : List α} {s : ℕ} (h : w.rotate s = w) : ∀ m, w.rotate (s * m) = w := by
  intro m
  induction m with
  | zero => simp
  | succ m ih => rw [Nat.mul_succ, ← rotate_rotate, ih, h]

lemma length_pow (r : ℕ) (v : List α) : ((replicate r v).flatten).length = r * v.length := by
  induction r with
  | zero => simp
  | succ r ih => simp [replicate_succ, flatten_cons, ih, Nat.succ_mul, add_comm]

lemma rotate_pow (r : ℕ) (v : List α) : ((replicate r v).flatten).rotate v.length = (replicate r v).flatten := by
  cases r with
  | zero => simp
  | succ r =>
    rw [replicate_succ, flatten_cons, rotate_append_length_eq]
    have e1 : (replicate r v).flatten ++ v = (replicate (r + 1) v).flatten := by
      rw [replicate_succ', flatten_append]; simp
    rw [e1, replicate_succ, flatten_cons]

theorem symm_iff_rotate (w : List α) (hw : w ≠ []) :
    Symm w ↔ ∃ s, 0 < s ∧ s < w.length ∧ w.rotate s = w := by
  constructor
  · rintro ⟨r, hr, v, hv⟩
    have hv0 : v ≠ [] := by rintro rfl; simp at hv; exact hw hv
    have hvp := length_pos_of_ne_nil hv0
    refine ⟨v.length, hvp, ?_, ?_⟩
    · rw [hv, length_pow]; nlinarith
    · rw [hv]; exact rotate_pow r v
  · rintro ⟨s, hs0, hsL, hrot⟩
    have hdL : Nat.gcd s w.length ∣ w.length := Nat.gcd_dvd_right s w.length
    have hd0 : 0 < Nat.gcd s w.length := Nat.gcd_pos_of_pos_left _ hs0
    have hds : Nat.gcd s w.length ≤ s := Nat.le_of_dvd hs0 (Nat.gcd_dvd_left s w.length)
    obtain ⟨m, -, hm⟩ := Nat.exists_mul_mod_eq_gcd (show Nat.gcd s w.length < w.length by omega)
    have hrd : w.rotate (Nat.gcd s w.length) = w := by
      rw [← hm, rotate_mod, rotate_mul_self hrot m]
    set d := Nat.gcd s w.length with hd
    have hper : ∀ i (h : i + d < w.length), w[i + d] = w[i]'(by omega) := by
      intro i h
      have hdrop : w.drop d ++ w.take d = w := by rw [← rotate_eq_drop_append_take (by omega)]; exact hrd
      have e1 : (w.drop d ++ w.take d)[i]? = w[i]? := by rw [hdrop]
      rw [getElem?_append_left (by simp; omega), getElem?_drop,
        getElem?_eq_getElem (by omega), getElem?_eq_getElem (by omega)] at e1
      have h2 := Option.some.inj e1
      simp only [Nat.add_comm d i] at h2
      exact h2
    obtain ⟨q, hq⟩ := hdL
    refine ⟨q, ?_, w.take d, pow_of_periodic d q w (by rw [hq, mul_comm]) hper⟩
    by_contra hq2
    have : q ≤ 1 := by omega
    have : w.length ≤ d := by rw [hq]; nlinarith
    omega

/-- Symmetry depends only on the necklace. -/
theorem symm_rotate (w : List α) (t : ℕ) : Symm (w.rotate t) ↔ Symm w := by
  rcases eq_or_ne w [] with rfl | hw
  · simp
  have hw' : w.rotate t ≠ [] := by simpa using hw
  rw [symm_iff_rotate _ hw', symm_iff_rotate _ hw, length_rotate]
  constructor
  · rintro ⟨s, h0, h1, h⟩
    refine ⟨s, h0, h1, ?_⟩
    have : (w.rotate t).rotate s = (w.rotate s).rotate t := by rw [rotate_rotate, rotate_rotate, add_comm]
    rw [this] at h
    exact rotate_eq_rotate.mp h
  · rintro ⟨s, h0, h1, h⟩
    refine ⟨s, h0, h1, ?_⟩
    rw [rotate_rotate, add_comm, ← rotate_rotate, h]

/-- Deleting colours from a rotation gives a rotation of the deleted word. -/
theorem filter_rotate (p : α → Bool) (w : List α) (t : ℕ) :
    ∃ t', (w.rotate t).filter p = (w.filter p).rotate t' := by
  rcases eq_or_ne w [] with rfl | hw
  · exact ⟨0, by simp⟩
  rw [← rotate_mod, rotate_eq_drop_append_take (Nat.le_of_lt (Nat.mod_lt _ (length_pos_of_ne_nil hw)))]
  set u := t % w.length
  have hsplit : w.filter p = (w.take u).filter p ++ (w.drop u).filter p := by
    rw [← filter_append, take_append_drop]
  refine ⟨((w.take u).filter p).length, ?_⟩
  rw [hsplit, rotate_append_length_eq, filter_append]

end Precarious
