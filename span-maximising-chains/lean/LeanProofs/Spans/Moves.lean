import LeanProofs.Spans.Basic

/-!
# Span-maximizing chains: the three moves

* swapping two lengths changes `Z` by `(l j - l i)(e^{iθ_i} - e^{iθ_j})`;
* swapping two adjacent turns `k, k+1` changes only the direction of segment `k+1`;
* moving the first segment and the first turn to the end turns `Z = l₀ + e^{i a₀} W` into `W + l₀ e^{iT}`.
-/

open Complex Finset Real

namespace Spans

variable {m : ℕ}

/-! ## Swapping two lengths -/

lemma Z_swap_lengths (l : Fin (m + 1) → ℝ) (a : Fin m → ℝ) {i j : Fin (m + 1)} (hij : i ≠ j) :
    Z (l ∘ Equiv.swap i j) a = Z l a + ((l j - l i : ℝ) : ℂ) * (e (θ a i) - e (θ a j)) := by
  have key : ∀ k : Fin (m + 1), ((l (Equiv.swap i j k) : ℝ) : ℂ) * e (θ a k) =
      (l k : ℂ) * e (θ a k) + (if k = i then ((l j - l i : ℝ) : ℂ) * e (θ a i) else 0) +
        (if k = j then ((l i - l j : ℝ) : ℂ) * e (θ a j) else 0) := by
    intro k
    by_cases hki : k = i
    · subst hki; simp [Equiv.swap_apply_left, hij]; push_cast; ring
    · by_cases hkj : k = j
      · subst hkj; simp [Equiv.swap_apply_right, hki]; push_cast; ring
      · simp [Equiv.swap_apply_of_ne_of_ne hki hkj, hki, hkj]
  unfold Z
  simp only [Function.comp_apply, key, sum_add_distrib, sum_ite_eq', mem_univ, if_true]
  push_cast; ring

/-! ## Swapping two adjacent turns -/

lemma ext_swap (a : Fin m → ℝ) {k : ℕ} (hk : k + 1 < m) (j : ℕ) :
    ext (a ∘ Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) j =
      ext a j + (if j = k then ext a (k + 1) - ext a k else 0) +
        (if j = k + 1 then ext a k - ext a (k + 1) else 0) := by
  unfold ext
  by_cases hjk : j = k
  · subst hjk
    simp only [dif_pos (by omega : j < m), dif_pos hk, Function.comp_apply, if_true,
      if_neg (by omega : j ≠ j + 1)]
    rw [Equiv.swap_apply_left]; ring
  · by_cases hjk1 : j = k + 1
    · subst hjk1
      simp only [dif_pos hk, dif_pos (by omega : k < m), Function.comp_apply, if_neg hjk, if_true]
      rw [Equiv.swap_apply_right]; ring
    · simp only [if_neg hjk, if_neg hjk1, add_zero]
      split_ifs with h
      · simp only [Function.comp_apply]
        rw [Equiv.swap_apply_of_ne_of_ne (by simp [Fin.ext_iff]; omega) (by simp [Fin.ext_iff]; omega)]
      · rfl

lemma θ_swap (a : Fin m → ℝ) {k : ℕ} (hk : k + 1 < m) (i : ℕ) :
    θ (a ∘ Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) i =
      θ a i + (if i = k + 1 then ext a (k + 1) - ext a k else 0) := by
  unfold θ
  simp only [ext_swap a hk, sum_add_distrib]
  rw [sum_ite_eq', sum_ite_eq']
  simp only [mem_range]
  by_cases h1 : i = k + 1
  · subst h1; simp
  · by_cases h2 : k + 1 < i
    · rw [if_pos (by omega), if_pos h2, if_neg h1]; ring
    · rw [if_neg (by omega), if_neg h2, if_neg h1]; ring

lemma Z_swap_turns (l : Fin (m + 1) → ℝ) (a : Fin m → ℝ) {k : ℕ} (hk : k + 1 < m) :
    Z l (a ∘ Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) =
      Z l a + (l ⟨k + 1, by omega⟩ : ℂ) * (e (θ a k + ext a (k + 1)) - e (θ a (k + 1))) := by
  have key : ∀ i : Fin (m + 1), (l i : ℂ) * e (θ (a ∘ Equiv.swap ⟨k, by omega⟩ ⟨k + 1, hk⟩) i) =
      (l i : ℂ) * e (θ a i) + (if i = (⟨k + 1, by omega⟩ : Fin (m + 1)) then
        (l ⟨k + 1, by omega⟩ : ℂ) * (e (θ a k + ext a (k + 1)) - e (θ a (k + 1))) else 0) := by
    intro i
    rw [θ_swap a hk]
    by_cases hi : (i : ℕ) = k + 1
    · have hfin : i = (⟨k + 1, by omega⟩ : Fin (m + 1)) := Fin.ext hi
      rw [if_pos hi, if_pos hfin, hfin]
      simp only [Fin.val_mk]
      have h2 : θ a (k + 1) + (ext a (k + 1) - ext a k) = θ a k + ext a (k + 1) := by
        rw [θ_succ]; ring
      rw [h2]; ring
    · rw [if_neg hi, if_neg (fun h => hi (by rw [h])), add_zero, add_zero]
  unfold Z
  simp only [key, sum_add_distrib, sum_ite_eq', mem_univ, if_true]

/-! ## Moving the first segment to the end -/

lemma ext_rot (a : Fin (m + 1) → ℝ) (j : ℕ) (hj : j < m) :
    ext (a ∘ finRotate (m + 1)) j = ext a (j + 1) := by
  unfold ext
  rw [dif_pos (by omega), dif_pos (by omega)]
  simp only [Function.comp_apply]
  rw [finRotate_of_lt hj]

lemma ext_rot_last (a : Fin (m + 1) → ℝ) : ext (a ∘ finRotate (m + 1)) m = ext a 0 := by
  unfold ext
  rw [dif_pos (by omega), dif_pos (by omega)]
  simp only [Function.comp_apply]
  rw [finRotate_last']

lemma θ_rot (a : Fin (m + 1) → ℝ) {i : ℕ} (hi : i ≤ m) :
    θ (a ∘ finRotate (m + 1)) i = θ a (i + 1) - ext a 0 := by
  unfold θ
  rw [sum_range_succ' (ext a)]
  rw [sum_congr rfl fun j hj => ext_rot a j (by simp at hj; omega)]
  ring

lemma θ_rot_T (a : Fin (m + 1) → ℝ) : θ (a ∘ finRotate (m + 1)) (m + 1) = T a := by
  rw [θ_succ, θ_rot a le_rfl, ext_rot_last]; unfold T; ring

/-- `W`: the chain after its first segment, seen from its own first direction. -/
noncomputable def Wtail (l : Fin (m + 2) → ℝ) (a : Fin (m + 1) → ℝ) : ℂ :=
  ∑ i : Fin (m + 1), (l i.succ : ℂ) * e (θ a (i + 1) - ext a 0)

lemma Z_head (l : Fin (m + 2) → ℝ) (a : Fin (m + 1) → ℝ) :
    Z l a = (l 0 : ℂ) + e (ext a 0) * Wtail l a := by
  unfold Z Wtail
  rw [Fin.sum_univ_succ, mul_sum]
  simp only [Fin.val_zero, θ_zero, Fin.val_succ]
  congr 1
  · simp [e]
  · refine sum_congr rfl fun i _ => ?_
    rw [← mul_assoc, mul_comm (e _), mul_assoc, ← e_add]; ring_nf

lemma Z_rot (l : Fin (m + 2) → ℝ) (a : Fin (m + 1) → ℝ) :
    Z (l ∘ finRotate (m + 2)) (a ∘ finRotate (m + 1)) = Wtail l a + (l 0 : ℂ) * e (T a) := by
  unfold Z Wtail
  rw [Fin.sum_univ_castSucc]
  simp only [Function.comp_apply, Fin.coe_castSucc, Fin.val_last]
  congr 1
  · refine sum_congr rfl fun i _ => ?_
    rw [θ_rot a (by omega)]
    congr 2
    congr 1
    ext
    rw [coe_finRotate_of_ne_last (Fin.castSucc_lt_last i).ne]
    simp
  · rw [finRotate_last, θ_rot_T]

end Spans
