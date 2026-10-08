import LeanProofs.Spans.Structure

/-!
# Span-maximizing chains: four segments (`a₄ = 3`)

With the shortest segment first, every optimum of four segments has one of three order patterns
(Proposition 3.1):

* `P1` (`p = 0231, q = 201`): `l₀ < l₃ < l₁ < l₂` and `a₁ < a₂ < a₀`;
* `P2` (`p = 0321, q = 201`): `l₀ < l₃ < l₂ < l₁` and `a₁ < a₂ < a₀`;
* `P3` (`p = 0231, q = 102`): `l₀ < l₃ < l₁ < l₂` and `a₁ < a₀ < a₂`.

The fourth structural candidate `(0321, 102)` is impossible. `Witness.lean` shows each pattern occurs.
-/

open Complex Finset Real

namespace Spans

/-- The three order patterns. -/
def P1 (l : Fin 4 → ℝ) (a : Fin 3 → ℝ) : Prop :=
  l 0 < l 3 ∧ l 3 < l 1 ∧ l 1 < l 2 ∧ a 1 < a 2 ∧ a 2 < a 0
def P2 (l : Fin 4 → ℝ) (a : Fin 3 → ℝ) : Prop :=
  l 0 < l 3 ∧ l 3 < l 2 ∧ l 2 < l 1 ∧ a 1 < a 2 ∧ a 2 < a 0
def P3 (l : Fin 4 → ℝ) (a : Fin 3 → ℝ) : Prop :=
  l 0 < l 3 ∧ l 3 < l 1 ∧ l 1 < l 2 ∧ a 1 < a 0 ∧ a 0 < a 2

lemma ext3 (a : Fin 3 → ℝ) : ext a 0 = a 0 ∧ ext a 1 = a 1 ∧ ext a 2 = a 2 := by
  simp [ext]

lemma θ3 (a : Fin 3 → ℝ) : θ a 1 = a 0 ∧ θ a 2 = a 0 + a 1 ∧ θ a 3 = a 0 + a 1 + a 2 := by
  simp [θ, sum_range_succ, ext]

/-- Proposition 3.1 (classification): with the shortest segment first, an optimum of four segments has one of
the three patterns. -/
theorem n4_classify {l : Fin 4 → ℝ} {a : Fin 3 → ℝ} (h : Admissible l a) (hopt : Optimal l a)
    (hmin : ∀ j, j ≠ 0 → l 0 < l j) : P1 l a ∨ P2 l a ∨ P3 l a := by
  have hm : 1 ≤ 3 := by norm_num
  have h31 : l 3 < l 1 := last_second_shortest (m := 2) h hopt hmin (by decide) (by decide)
  have h32 : l 3 < l 2 := last_second_shortest (m := 2) h hopt hmin (by decide) (by decide)
  have h03 : l 0 < l 3 := hmin 3 (by decide)
  have hd := first_turn_descends (m := 3) h hopt hm (by norm_num) h03
  have ha := last_turn_ascends (m := 2) h hopt le_rfl hmin
  obtain ⟨e0, e1, e2⟩ := ext3 a
  simp only [e0, e1, show (2 - 1 : ℕ) = 1 by rfl] at hd ha
  rw [e2] at ha
  have h12 : l 1 ≠ l 2 := fun he => absurd (h.linj he) (by decide)
  have h02 : a 0 ≠ a 2 := fun he => absurd (h.ainj he) (by decide)
  rcases lt_or_gt_of_ne h12 with hl | hl <;> rcases lt_or_gt_of_ne h02 with hq | hq
  · exact Or.inr (Or.inr ⟨h03, h31, hl, hd, hq⟩)
  · exact Or.inl ⟨h03, h31, hl, ha, hq⟩
  · -- the excluded candidate (0321, 102): l₂ < l₁ needs 2φ < θ₁ + θ₂, but φ > T/2
    exfalso
    have hne : (2 : Fin 4) ≠ 1 := by decide
    have c := (lt_iff_closer h hopt hm hne).1 hl
    obtain ⟨t1, t2, t3⟩ := θ3 a
    simp only [Fin.val_one, Fin.val_two] at c
    rw [t1, t2] at c
    have hpos := h.apos 1
    have := (farther_iff (by linarith : a 0 < a 0 + a 1)).1 c
    have hhalf := half_lt_arg h hopt hm (hmin _ (by decide))
    unfold T at hhalf
    rw [t3] at hhalf
    linarith
  · exact Or.inr (Or.inl ⟨h03, h32, hl, ha, hq⟩)

/-! ## The four-segment displacement in closed form -/

lemma Z4 (l : Fin 4 → ℝ) (a : Fin 3 → ℝ) :
    Z l a = (l 0 : ℂ) + l 1 * e (a 0) + l 2 * (e (a 0) * e (a 1)) + l 3 * (e (a 0) * e (a 1) * e (a 2)) := by
  obtain ⟨t1, t2, t3⟩ := θ3 a
  unfold Z
  rw [Fin.sum_univ_four]
  have v1 : ((1 : Fin 4) : ℕ) = 1 := rfl
  have v2 : ((2 : Fin 4) : ℕ) = 2 := rfl
  have v3 : ((3 : Fin 4) : ℕ) = 3 := rfl
  have v0 : ((0 : Fin 4) : ℕ) = 0 := rfl
  rw [v0, v1, v2, v3, θ_zero, t1, t2, t3, e_add, e_add, e_add]
  simp [e]

lemma e_mul_neg (x : ℝ) : e x * e (-x) = 1 := by rw [← e_add, add_neg_cancel]; simp [e]

lemma conj_e (x : ℝ) : (starRingEnd ℂ) (e x) = e (-x) := by
  unfold e; rw [← Complex.exp_conj]; congr 1; simp [Complex.conj_ofReal]

/-- Reversing both lists conjugates the displacement and rotates it: the span is unchanged. -/
lemma norm_Z_rev (l : Fin 4 → ℝ) (a : Fin 3 → ℝ) :
    ‖Z (l ∘ Fin.revPerm) (a ∘ Fin.revPerm)‖ = ‖Z l a‖ := by
  have key : Z (l ∘ Fin.revPerm) (a ∘ Fin.revPerm) =
      e (a 0) * e (a 1) * e (a 2) * (starRingEnd ℂ) (Z l a) := by
    rw [Z4, Z4]
    simp only [Function.comp_apply, Fin.revPerm_apply]
    simp only [map_add, map_mul, Complex.conj_ofReal, conj_e]
    have r0 : Fin.rev (0 : Fin 4) = 3 := rfl
    have r1 : Fin.rev (1 : Fin 4) = 2 := rfl
    have r2 : Fin.rev (2 : Fin 4) = 1 := rfl
    have r3 : Fin.rev (3 : Fin 4) = 0 := rfl
    have s0 : Fin.rev (0 : Fin 3) = 2 := rfl
    have s1 : Fin.rev (1 : Fin 3) = 1 := rfl
    have s2 : Fin.rev (2 : Fin 3) = 0 := rfl
    rw [r0, r1, r2, r3, s0, s1, s2]
    linear_combination (-(↑(l 1) * e (a 1) * e (a 2) + ↑(l 2) * e (a 2) + ↑(l 3))) * e_mul_neg (a 0) +
      (-(↑(l 2) * e (a 2) + ↑(l 3)) * e (a 0) * e (-a 0)) * e_mul_neg (a 1) +
      (-(↑(l 3)) * e (a 0) * e (-a 0) * e (a 1) * e (-a 1)) * e_mul_neg (a 2)
  rw [key, norm_mul, norm_mul, norm_mul, norm_e, norm_e, norm_e, Complex.norm_conj]; ring

end Spans
