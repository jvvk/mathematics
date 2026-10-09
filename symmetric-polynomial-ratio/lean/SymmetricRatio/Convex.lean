import SymmetricRatio.Roots

/-!
# MO 467261: discrete convexity of `P_ℓ / P_{ℓ+1}` on `[0, ∞)`

Partial fractions over the `ℓ+1` real roots `r_i < 0` of `P_{ℓ+1}` give
`P_ℓ/P_{ℓ+1} = ∑ c_i/(t - r_i)` with `c_i > 0` (the sign of the Wronskian at `r_i`),
so the second difference at `t ≥ 1` is `∑ 2 c_i / (a_i (a_i^2 - 1)) > 0`, `a_i = t - r_i > 1`.
-/

open Polynomial Finset

namespace Haddou

theorem second_difference_pos (N : ℕ) {y : ℝ} (hy : 0 < y) (ℓ : ℕ) {t : ℝ} (ht : 1 ≤ t) :
    let f : ℝ → ℝ := fun s => (P N y ℓ).eval s / (P N y (ℓ + 1)).eval s
    0 < f (t - 1) + f (t + 1) - 2 * f t := by
  intro f
  obtain ⟨r, hr, hroot, hneg⟩ := real_rooted N hy (ℓ + 1)
  set S := range (ℓ + 1)
  have hinj : Set.InjOn r (S : Set ℕ) := by
    intro i hi k hk hik
    simp only [S, coe_range, Set.mem_Iio] at hi hk
    by_contra hne
    rcases lt_or_gt_of_ne hne with h | h
    · exact (hr i k h hk).ne hik
    · exact (hr k i h hi).ne hik.symm
  set lc := (P N y (ℓ + 1)).leadingCoeff
  have hlc : 0 < lc := leadingCoeff_P_pos N hy (ℓ + 1)
  set w : ℕ → ℝ := fun i => Lagrange.nodalWeight S r i
  set c : ℕ → ℝ := fun i => (P N y ℓ).eval (r i) * w i / lc
  -- partial fractions
  have hpf : ∀ s : ℝ, (∀ i ∈ S, s ≠ r i) → f s = ∑ i ∈ S, c i / (s - r i) := by
    intro s hs
    have hdeg : (P N y ℓ).degree < #S := by
      rw [card_range, degree_eq_natDegree (P_ne_zero N hy.le ℓ), natDegree_P N hy.ne' ℓ]
      exact_mod_cast Nat.lt_succ_self ℓ
    have hint := Lagrange.eq_interpolate hinj hdeg
    have hnod : (Lagrange.nodal S r).eval s ≠ 0 := by
      rw [Lagrange.eval_nodal]
      exact Finset.prod_ne_zero_iff.2 fun i hi => sub_ne_zero.2 (hs i hi)
    have hnum : (P N y ℓ).eval s =
        (Lagrange.nodal S r).eval s * ∑ i ∈ S, (P N y ℓ).eval (r i) * w i * (s - r i)⁻¹ := by
      conv_lhs => rw [hint]
      rw [Lagrange.interpolate_apply, eval_finsetSum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i hi => ?_
      rw [eval_mul, eval_C, Lagrange.eval_basis_not_at_node hi (hs i hi)]
      ring
    have hden : (P N y (ℓ + 1)).eval s = lc * (Lagrange.nodal S r).eval s := by
      conv_lhs => rw [P_factor N hy (ℓ + 1) r hr hroot]
      rw [eval_mul, eval_C]
    simp only [f]
    rw [hnum, hden, Finset.mul_sum, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [c]
    field_simp
  -- positivity of the residues
  have hc : ∀ i ∈ S, 0 < c i := by
    intro i hi
    have hi' := mem_range.1 hi
    have hW := W_pos N hy ℓ (r i)
    simp only [W, eval_sub, eval_mul, hroot i hi', zero_mul, sub_zero] at hW
    rw [P_deriv_at_root N hy (ℓ + 1) r hr hroot hi'] at hW
    set Pr := ∏ j ∈ S.erase i, (r i - r j)
    have hw : w i = Pr⁻¹ := by
      simp only [w, Lagrange.nodalWeight, Pr, Finset.prod_inv_distrib]
    have h1 : 0 < Pr * (P N y ℓ).eval (r i) := by
      have : 0 < lc * (Pr * (P N y ℓ).eval (r i)) := by linarith [hW, show lc * Pr * (P N y ℓ).eval (r i) = lc * (Pr * (P N y ℓ).eval (r i)) by ring]
      exact pos_of_mul_pos_right this hlc.le
    have hPr : Pr ≠ 0 := by rintro h; rw [h, zero_mul] at h1; exact lt_irrefl 0 h1
    simp only [c, hw]
    have : (P N y ℓ).eval (r i) * Pr⁻¹ = (Pr * (P N y ℓ).eval (r i)) / Pr ^ 2 := by
      field_simp
    rw [this]; positivity
  -- each node is negative, so every evaluation point is off the nodes
  have hoff : ∀ s, 0 ≤ s → ∀ i ∈ S, s ≠ r i := fun s hs i hi h =>
    by have := hneg i (mem_range.1 hi); linarith
  rw [hpf (t - 1) (hoff _ (by linarith)), hpf (t + 1) (hoff _ (by linarith)),
    hpf t (hoff _ (by linarith)), Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_pos (fun i hi => ?_) ⟨0, mem_range.2 (Nat.succ_pos ℓ)⟩
  have ha : 1 < t - r i := by have := hneg i (mem_range.1 hi); linarith
  set A := t - r i
  have e1 : t - 1 - r i = A - 1 := by ring
  have e2 : t + 1 - r i = A + 1 := by ring
  rw [e1, e2]
  have hA1 : 0 < A - 1 := by linarith
  have key : c i / (A - 1) + c i / (A + 1) - 2 * (c i / A) = 2 * c i / (A * (A - 1) * (A + 1)) := by
    field_simp; ring
  rw [key]
  have := hc i hi
  positivity

end Haddou
